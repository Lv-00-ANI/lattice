import Mathlib
import Lattice.Lib.LinearAlgebra.RealL2Operator
import Lattice.Lib.LinearAlgebra.RealMatrixStability
/-!
# LATTICE: 算子幂级数极限（Neumann 级数 / 迭代收敛常数）

本文件把「`‖T‖ < 1` 时算子几何级数收敛」这一套结论形式化，用于：
  1. 标量几何和闭式与上界（`geom_sum_eq'`、`geom_sum_le_inv`）；
  2. 算子部分和的范数上界 `‖∑_{k<N} T^k‖ ≤ (1-‖T‖)⁻¹`（`op_geom_sum_norm_le`）；
  3. 算子幂级数的可和性 / 和 = `(1-T)⁻¹`（Neumann 级数，
     `summable_op_pow`、`tsum_op_pow_eq_inverse`、`one_sub_mul_tsum`、`tsum_mul_one_sub`）；
  4. 幂的零极限 `T^n → 0`（`op_pow_tendsto_zero`）；
  5. **填补 `RealMatrixStability` 中标注为「未证」的极限界**（该文件 docstring 明说
     `‖b‖/(1-‖T‖)` 未证）：本文件证明
     `iterateStep_norm_le_inv : ‖iterateStep T b n‖ ≤ ‖b‖ / (1 - ‖T‖)`，
     以及乘常数形式的 `iterateStep_norm_le_inv'`。

诚实标注与降级（无 sorry / axiom / admit）：
  · 充分条件用的是**严格算子范数** `‖T‖ < 1`；**谱半径判据 `ρ(T) < 1` 未证 / 降级**
    ——它严格弱于 `‖T‖ < 1`（例：‖T‖ 可以 >1 而 ρ(T) < 1），需要一般算子的
    谱半径理论（Gelfand 公式），本仓库只在 `RealSpectralRadius` 中对**对角矩阵**
    给出了谱半径的完整刻画，一般算子情形仍是**未做**；
  · **完备性 `[CompleteSpace E]` 只在无穷 `tsum` 相关结论中出现**（可和性与
    `∑'` 的闭式）；有限部分和的范数上界（`op_geom_sum_norm_le`、
    `iterateStep_norm_le_inv`）**不需要完备性**；
  · 未做：级数的**误差界**（`‖∑_{k≥N} T^k‖ ≤ …`）、`T ↦ (1-T)⁻¹` 的连续性
    （Neumann 级数对扰动的 Lipschitz 界）；
  · 矩阵特化（`matCLME (A^k)` 形式）未重复，直接由 `T = matCLME A` 代入即可；
  · 只读复用 `RealL2Operator` / `RealMatrixStability`，不修改它们。
-/

noncomputable section

open scoped Topology

open Lattice.Lib.LinearAlgebra.RealMatrixStability

namespace Lattice

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 一、标量几何级数 -/

/-- 几何和闭式：`r ≠ 1` 时 `∑_{k<n} r^k = (1 - r^n) / (1 - r)`。
（回收 `geom_sum_mul`，两端同乘 `1 - r` 后作恒等变形。） -/
theorem geom_sum_eq' (r : ℝ) (n : ℕ) (hr : r ≠ 1) :
    ∑ k in Finset.range n, r ^ k = (1 - r ^ n) / (1 - r) := by
  have h1 : (1 : ℝ) - r ≠ 0 := by
    intro hh
    exact hr (by linarith)
  rw [eq_div_iff h1]
  have h := geom_sum_mul r n
  linear_combination -h

/-- 几何和上界：`0 ≤ r < 1` 时 `∑_{k<n} r^k ≤ (1 - r)⁻¹`（对一切 `n` 一致）。 -/
theorem geom_sum_le_inv {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ k in Finset.range n, r ^ k ≤ (1 - r)⁻¹ := by
  have hpos : 0 < 1 - r := by linarith
  rw [geom_sum_eq' r n (by linarith), div_le_iff₀ hpos,
    inv_mul_cancel₀ (ne_of_gt hpos)]
  linarith [pow_nonneg h0 n]

/-! ## 二、算子部分和与 Neumann 级数 -/

/-- **算子几何部分和界**：`‖T‖ < 1` 时 `‖∑_{k<N} T^k‖ ≤ (1 - ‖T‖)⁻¹`（一致于 `N`）。 -/
theorem op_geom_sum_norm_le (T : E →L[ℝ] E) (h : ‖T‖ < 1) (N : ℕ) :
    ‖∑ k in Finset.range N, T ^ k‖ ≤ (1 - ‖T‖)⁻¹ := by
  calc ‖∑ k in Finset.range N, T ^ k‖ ≤ ∑ k in Finset.range N, ‖T ^ k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k in Finset.range N, ‖T‖ ^ k := by
        apply Finset.sum_le_sum
        intro k _
        exact op_norm_pow_le T k
    _ ≤ (1 - ‖T‖)⁻¹ := geom_sum_le_inv (norm_nonneg T) h N

/-- **算子幂级数可和**：`‖T‖ < 1` 时 `∑_k T^k` 可和（需完备性）。 -/
theorem summable_op_pow [CompleteSpace E] (T : E →L[ℝ] E) (h : ‖T‖ < 1) :
    Summable (fun k : ℕ => T ^ k) :=
  summable_geometric_of_norm_lt_one h

/-- **Neumann 级数闭式**：`∑_k T^k = Ring.inverse (1 - T)`（即 `(1-T)⁻¹`）。 -/
theorem tsum_op_pow_eq_inverse [CompleteSpace E] (T : E →L[ℝ] E) (h : ‖T‖ < 1) :
    ∑' k : ℕ, T ^ k = Ring.inverse (1 - T) :=
  geom_series_eq_inverse T h

/-- **左逆关系**：`(1 - T) * ∑_k T^k = 1`（回收 `mul_neg_geom_series`）。 -/
theorem one_sub_mul_tsum [CompleteSpace E] (T : E →L[ℝ] E) (h : ‖T‖ < 1) :
    (1 - T) * ∑' k : ℕ, T ^ k = 1 :=
  mul_neg_geom_series T h

/-- **右逆关系**：`(∑_k T^k) * (1 - T) = 1`（回收 `geom_series_mul_neg`）。 -/
theorem tsum_mul_one_sub [CompleteSpace E] (T : E →L[ℝ] E) (h : ‖T‖ < 1) :
    (∑' k : ℕ, T ^ k) * (1 - T) = 1 :=
  geom_series_mul_neg T h

/-- **幂零极限**：`‖T‖ < 1` 时 `T^n → 0`（不需要完备性；`NormedRing` 即够）。 -/
theorem op_pow_tendsto_zero (T : E →L[ℝ] E) (h : ‖T‖ < 1) :
    Filter.Tendsto (fun n : ℕ => T ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

/-! ## 三、填补 `RealMatrixStability` 的未证缺口：迭代累积极限界 -/

/-- **迭代累积的极限界（除法形式）**：`‖T‖ < 1` 时
`‖iterateStep T b n‖ ≤ ‖b‖ / (1 - ‖T‖)`，对一切 `n` 一致。
这是 `RealMatrixStability` 中标注为「未证」的极限界的显式证明：
回收 `iterateStep_norm_le` 的有限和，再用算子几何和一致上界 `geom_sum_le_inv` 收紧。 -/
theorem iterateStep_norm_le_inv (T : E →L[ℝ] E) (b : E) (h : ‖T‖ < 1) (n : ℕ) :
    ‖iterateStep T b n‖ ≤ ‖b‖ / (1 - ‖T‖) := by
  refine le_trans (iterateStep_norm_le T b n) ?_
  rw [← Finset.sum_mul]
  calc (∑ k in Finset.range n, ‖T‖ ^ k) * ‖b‖
      ≤ (1 - ‖T‖)⁻¹ * ‖b‖ :=
        mul_le_mul_of_nonneg_right (geom_sum_le_inv (norm_nonneg T) h n) (norm_nonneg b)
    _ = ‖b‖ / (1 - ‖T‖) := by rw [div_eq_mul_inv, mul_comm]

/-- **迭代累积的极限界（乘常数形式）**：`‖T‖ < 1` 时
`‖iterateStep T b n‖ ≤ (1 - ‖T‖)⁻¹ * ‖b‖`。 -/
theorem iterateStep_norm_le_inv' (T : E →L[ℝ] E) (b : E) (h : ‖T‖ < 1) (n : ℕ) :
    ‖iterateStep T b n‖ ≤ (1 - ‖T‖)⁻¹ * ‖b‖ :=
  le_trans (iterateStep_norm_le_inv T b h n)
    (le_of_eq (by rw [div_eq_mul_inv, mul_comm]))

/-! ## 四、注：诚实降级
  · 全部结论的充分条件是**严格算子范数** `‖T‖ < 1`；
    **谱半径判据 `ρ(T) < 1` 未证 / 降级**（需要一般算子的 Gelfand 公式与复谱理论，
    本仓库仅在 `RealSpectralRadius` 中对**对角矩阵**完成了 `ρ = ‖·‖` 的刻画）；
  · `[CompleteSpace E]` 仅用于无穷 `tsum` 命题；有限部分和结论不需要完备性；
  · 未做：Neumann 级数的余项误差界、`(1-T)⁻¹` 关于 `T` 的连续性。 -/

end Lattice
