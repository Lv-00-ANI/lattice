import Mathlib
import Lattice.Lib.LinearAlgebra.RealL2Operator
/-!
# LATTICE: 矩阵/算子稳定性（扰动界、收缩、累积与乘性放大）

本文件在 `RealL2Operator` 的算子范数基础上给出**数值稳定性**的代数界：

  1. `perturbation_bound`：`‖(A + E) x - A x‖ ≤ ‖E‖ ‖x‖`（回收 `op_apply_le`）；
     `matrixStability_relative_perturbation_bound`：`x ≠ 0` 时前向相对误差 `≤ ‖E‖`；
  2. `op_norm_pow_le_simple` / `matrixStability_contraction_pow_bound`：`‖T^n‖ ≤ ‖T‖^n`、
     `‖T^n x‖ ≤ c^n ‖x‖`（`‖T‖ ≤ c`），回收 `RealL2Operator`；
  3. `contraction_decay`：`‖T‖ < 1` ⟹ `‖T‖^n → 0`（几何衰减）；
  4. `iterateStep`：迭代 `x_{n+1} = T x_n + b`，`x_0 = 0`；**`iterateStep_norm_le`**：
     `‖x_n‖ ≤ ∑_{k<n} ‖T‖^k ‖b‖`（扰动累积界，回收 `op_apply_le` + 归纳）；
  5. `prod_one_add_le_exp`：`∏ (1 + ε_i) ≤ exp (∑ ε_i)`（`ε_i ≥ 0`，用 `Real.add_one_le_exp`
     + `Real.exp_sum`）——每步相对扰动的乘性放大的指数界。

诚实标注（无 sorry / axiom / admit）：
- **条件数形式的相对误差界未做**：`‖Δx‖/‖x‖ ≤ cond(A) ‖E‖/‖A‖` 需要**可逆性 /
  逆算子理论**（`A⁻¹` 的有界性、`‖A⁻¹‖` 的存在性）；本文件只给**前向误差**
  `‖(A+E)x - Ax‖ ≤ ‖E‖‖x‖` 与相对版本 `≤ ‖E‖`，不声称条件数界。
- `contraction_decay` 只给「`‖T‖^n → 0`」这一纯数列结论；**不动点存在性未做**
  （需完备性，LATTICE 的 `RealBanach` 负责，本文件不重复）。
- 迭代界 `∑_{k<n} ‖T‖^k ‖b‖` 是**逐项绝对值之和**的上界（非 sharp）；
  `n → ∞` 的收敛和 `‖b‖/(1-‖T‖)` 未证（需要级数极限）。
- `prod_one_add_le_exp` 需要 `ε_i ≥ 0`（否则 `1 + ε_i` 可能为负，乘积不等式失效）。
- 只读复用 `RealL2Operator`，不修改它。
- **命名避让（为避免跨文件命名冲突而前缀化）**：`contraction_pow_bound` 与
  `RealConvergence.contraction_pow_bound` 重名、`relative_perturbation_bound` 与
  `RealConditionNumber.relative_perturbation_bound` 重名，故分别改名为
  `matrixStability_contraction_pow_bound` / `matrixStability_relative_perturbation_bound`。
-/

noncomputable section

open scoped Topology

namespace Lattice.Lib.LinearAlgebra.RealMatrixStability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 一、算子扰动 -/

/-- 扰动恒等式：`(A + E) x = A x + E x`。 -/
theorem perturbation_identity (A Epart : E →L[ℝ] E) (x : E) :
    (A + Epart) x = A x + Epart x := rfl

/-- **前向扰动界**：`‖(A + E) x - A x‖ ≤ ‖E‖ ‖x‖`。 -/
theorem perturbation_bound (A Epart : E →L[ℝ] E) (x : E) :
    ‖(A + Epart) x - A x‖ ≤ ‖Epart‖ * ‖x‖ := by
  have h : (A + Epart) x - A x = Epart x := by simp
  rw [h]
  exact op_apply_le Epart x

/-- **相对前向误差界**：`x ≠ 0` 时 `‖(A + E) x - A x‖ / ‖x‖ ≤ ‖E‖`。
（命名前缀 `matrixStability_`：避免与 `RealConditionNumber.relative_perturbation_bound` 冲突。） -/
theorem matrixStability_relative_perturbation_bound (A Epart : E →L[ℝ] E) (x : E) (hx : x ≠ 0) :
    ‖(A + Epart) x - A x‖ / ‖x‖ ≤ ‖Epart‖ := by
  rw [div_le_iff₀ (norm_pos_iff.mpr hx)]
  exact perturbation_bound A Epart x

/-! ## 二、收缩与幂增长 -/

/-- **幂增长界**：`‖T^n‖ ≤ ‖T‖^n`（回收 `RealL2Operator.op_norm_pow_le`）。 -/
theorem op_norm_pow_le_simple (T : E →L[ℝ] E) (n : ℕ) : ‖T ^ n‖ ≤ ‖T‖ ^ n :=
  op_norm_pow_le T n

/-- **强收缩下的幂作用界**：`‖T‖ ≤ c ⟹ ‖T^n x‖ ≤ c^n ‖x‖`。
（命名前缀 `matrixStability_`：避免与 `RealConvergence.contraction_pow_bound` 冲突。） -/
theorem matrixStability_contraction_pow_bound (T : E →L[ℝ] E) {c : ℝ} (hc : 0 ≤ c)
    (h : ‖T‖ ≤ c) (n : ℕ) (x : E) : ‖(T ^ n) x‖ ≤ c ^ n * ‖x‖ :=
  op_norm_pow_apply_le_of_le hc h n x

/-- **几何衰减**：`‖T‖ < 1 ⟹ ‖T‖^n → 0`。 -/
theorem contraction_decay (T : E →L[ℝ] E) (h : ‖T‖ < 1) :
    Filter.Tendsto (fun n : ℕ => ‖T‖ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg T) h

/-- 收缩的幂有界：`‖T‖ < 1 ⟹ ‖T^n‖ ≤ 1`。 -/
theorem contraction_pow_le_one (T : E →L[ℝ] E) (h : ‖T‖ < 1) (n : ℕ) : ‖T ^ n‖ ≤ 1 :=
  le_trans (op_norm_pow_le T n) (pow_le_one₀ (norm_nonneg T) (le_of_lt h))

/-! ## 三、迭代累积 -/

/-- 迭代 `x_{n+1} = T x_n + b`，`x_0 = 0`。 -/
def iterateStep (T : E →L[ℝ] E) (b : E) : ℕ → E
  | 0 => 0
  | n + 1 => T (iterateStep T b n) + b

@[simp] theorem iterateStep_zero (T : E →L[ℝ] E) (b : E) : iterateStep T b 0 = 0 := rfl

@[simp] theorem iterateStep_succ (T : E →L[ℝ] E) (b : E) (n : ℕ) :
    iterateStep T b (n + 1) = T (iterateStep T b n) + b := rfl

/-- **扰动累积界**：`‖x_n‖ ≤ ∑_{k<n} ‖T‖^k ‖b‖`。 -/
theorem iterateStep_norm_le (T : E →L[ℝ] E) (b : E) (n : ℕ) :
    ‖iterateStep T b n‖ ≤ ∑ k in Finset.range n, ‖T‖ ^ k * ‖b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterateStep_succ]
      calc ‖T (iterateStep T b n) + b‖ ≤ ‖T (iterateStep T b n)‖ + ‖b‖ := norm_add_le _ _
        _ ≤ ‖T‖ * ‖iterateStep T b n‖ + ‖b‖ := by
              have := op_apply_le T (iterateStep T b n)
              linarith
        _ ≤ ‖T‖ * (∑ k in Finset.range n, ‖T‖ ^ k * ‖b‖) + ‖b‖ := by
              have hT := norm_nonneg T
              nlinarith
        _ = ∑ k in Finset.range n, ‖T‖ ^ (k + 1) * ‖b‖ + ‖b‖ := by
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = ∑ k in Finset.range (n + 1), ‖T‖ ^ k * ‖b‖ := by
              rw [Finset.sum_range_succ']
              ring

/-! ## 四、乘性放大的指数界 -/

/-- **乘性放大 ≤ 指数和**：`∏ i, (1 + ε i) ≤ exp (∑ i, ε i)`（`ε i ≥ 0`）。 -/
theorem prod_one_add_le_exp {ι : Type*} [Fintype ι] (eps : ι → ℝ) (heps : ∀ i, 0 ≤ eps i) :
    ∏ i, (1 + eps i) ≤ Real.exp (∑ i, eps i) := by
  calc ∏ i, (1 + eps i) ≤ ∏ i, Real.exp (eps i) :=
        Finset.prod_le_prod (fun i _ => by linarith [heps i])
          (fun i _ => by linarith [Real.add_one_le_exp (eps i)])
    _ = Real.exp (∑ i, eps i) := by rw [Real.exp_sum]

end Lattice.Lib.LinearAlgebra.RealMatrixStability