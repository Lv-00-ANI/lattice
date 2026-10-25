import Mathlib

/-!
# LATTICE: 连续线性算子的 L2 / 算子范数

深度网络的"深层传播"在忽略非线性时就是对算子的反复复合：`x ↦ T^n x`。本文件把
算子范数（= L2 意义下的最大放大倍数）这套基本事实形式化，作为 LATTICE 里
"深度方向爆炸/衰减"判据的**线性代数内核**：

  1. `op_apply_le`：`‖T x‖ ≤ ‖T‖ ‖x‖`（定义性不等式，mathlib 的 `le_opNorm`）；
  2. `op_norm_comp_le`：**次乘性** `‖T.comp S‖ ≤ ‖T‖ ‖S‖`（本文件自行从 1 证明，
     不依赖 mathlib 的 `opNorm_comp_le`，以避免参数顺序歧义）；
  3. `op_norm_pow_le`：`‖T^n‖ ≤ ‖T‖^n`（由 2 归纳）；
  4. `op_norm_pow_apply_le`：`‖T^n x‖ ≤ ‖T‖^n ‖x‖`（深度 n 的梯度/信号放大上界）；
  5. `op_norm_comp_apply_le`：`‖T (S x)‖ ≤ ‖T‖‖S‖‖x‖`；
  6. 距离/失真：`op_dist_le`：`‖T x - T y‖ ≤ ‖T‖ ‖x - y‖`（线性 ⟹ 全局 Lipschitz）；
  7. 深层收缩：`op_norm_pow_apply_le_of_le`：`‖T‖ ≤ c` ⟹ `‖T^n x‖ ≤ c^n ‖x‖`；
  8. 幂零/零算子边界：`op_norm_zero`、`op_norm_nonneg`、`op_norm_id_le`、
     `op_norm_id`（`E` 非平凡时 `‖id‖ = 1`）、`op_norm_smul_le`。

**诚实边界**：
- 本文件是**纯算子范数代数**：所有结论对任意（不必完备的）赋范空间成立，
  **不使用**完备性、自伴性、谱定理或特征值；
- **谱半径公式 `ρ(T) = lim ‖T^n‖^{1/n}` 未做**（需要复分析/谱理论）；
- **不动点存在性未做**（需要完备性 + `‖T‖ < 1`；LATTICE 已有 `RealBanach` 处理，
  本文件不重复）；
- **对称/自伴算子的范数 = 最大特征值 未做**（需要内积空间与谱定理）。
- 无矩阵指标类型的特化（那是 `RealMatrixNorm` 的职责）。

无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ## 基本不等式 -/

/-- 算子范数的定义性不等式：`‖T x‖ ≤ ‖T‖ ‖x‖`。 -/
theorem op_apply_le (T : E →L[ℝ] F) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ :=
  T.le_opNorm x

/-- 算子范数非负。 -/
theorem op_norm_nonneg (T : E →L[ℝ] F) : 0 ≤ ‖T‖ := norm_nonneg T

/-- 零算子的算子范数为 0。 -/
theorem op_norm_zero : ‖(0 : E →L[ℝ] F)‖ = 0 := ContinuousLinearMap.opNorm_zero

/-- 恒等算子的算子范数不超过 1。 -/
theorem op_norm_id_le : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 :=
  ContinuousLinearMap.norm_id_le

/-- `E` 非平凡时恒等算子的算子范数恰为 1。 -/
theorem op_norm_id [Nontrivial E] : ‖ContinuousLinearMap.id ℝ E‖ = 1 :=
  ContinuousLinearMap.norm_id

/-- 实标量齐次（用 `NormedSpace` 实例的 `norm_smul_le`）。 -/
theorem op_norm_smul_le (c : ℝ) (T : E →L[ℝ] F) : ‖c • T‖ ≤ ‖c‖ * ‖T‖ :=
  norm_smul_le c T

/-! ## 次乘性 -/

/-- **次乘性**：`‖T.comp S‖ ≤ ‖T‖ ‖S‖`（自行从 `opNorm_le_bound` 证明）。 -/
theorem op_norm_comp_le (S : E →L[ℝ] F) (T : F →L[ℝ] G) :
    ‖T.comp S‖ ≤ ‖T‖ * ‖S‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (T.comp S) (mul_nonneg (norm_nonneg T) (norm_nonneg S))
    (fun x => ?_)
  calc ‖(T.comp S) x‖ = ‖T (S x)‖ := rfl
    _ ≤ ‖T‖ * ‖S x‖ := T.le_opNorm (S x)
    _ ≤ ‖T‖ * (‖S‖ * ‖x‖) := by
        have h := S.le_opNorm x
        have hT : 0 ≤ ‖T‖ := norm_nonneg T
        nlinarith
    _ = (‖T‖ * ‖S‖) * ‖x‖ := by ring

/-- 复合在向量上的界：`‖T (S x)‖ ≤ ‖T‖ ‖S‖ ‖x‖`。 -/
theorem op_norm_comp_apply_le (S : E →L[ℝ] F) (T : F →L[ℝ] G) (x : E) :
    ‖T (S x)‖ ≤ ‖T‖ * ‖S‖ * ‖x‖ := by
  calc ‖T (S x)‖ ≤ ‖T‖ * ‖S x‖ := T.le_opNorm (S x)
    _ ≤ ‖T‖ * (‖S‖ * ‖x‖) := by
        have h := S.le_opNorm x
        have hT : 0 ≤ ‖T‖ := norm_nonneg T
        nlinarith
    _ = ‖T‖ * ‖S‖ * ‖x‖ := by ring

/-! ## 幂与深层传播 -/

/-- **幂增长界**：`‖T^n‖ ≤ ‖T‖^n`。 -/
theorem op_norm_pow_le (T : E →L[ℝ] E) : ∀ n : ℕ, ‖T ^ n‖ ≤ ‖T‖ ^ n
  | 0 => by
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
  | n + 1 => by
      rw [pow_succ, pow_succ]
      calc ‖T ^ n * T‖ = ‖(T ^ n).comp T‖ := rfl
        _ ≤ ‖T ^ n‖ * ‖T‖ := op_norm_comp_le T (T ^ n)
        _ ≤ ‖T‖ ^ n * ‖T‖ := mul_le_mul_of_nonneg_right (op_norm_pow_le T n) (norm_nonneg T)
        _ = ‖T‖ ^ (n + 1) := by ring

/-- **深度 n 的信号放大上界**：`‖T^n x‖ ≤ ‖T‖^n ‖x‖`。 -/
theorem op_norm_pow_apply_le (T : E →L[ℝ] E) (n : ℕ) (x : E) :
    ‖(T ^ n) x‖ ≤ ‖T‖ ^ n * ‖x‖ := by
  calc ‖(T ^ n) x‖ ≤ ‖T ^ n‖ * ‖x‖ := (T ^ n).le_opNorm x
    _ ≤ ‖T‖ ^ n * ‖x‖ := mul_le_mul_of_nonneg_right (op_norm_pow_le T n) (norm_nonneg x)

/-- 若 `‖T‖ ≤ c`，则深度 n 的放大不超过 `c^n`。 -/
theorem op_norm_pow_apply_le_of_le {T : E →L[ℝ] E} {c : ℝ} (_hc : 0 ≤ c) (h : ‖T‖ ≤ c)
    (n : ℕ) (x : E) : ‖(T ^ n) x‖ ≤ c ^ n * ‖x‖ := by
  calc ‖(T ^ n) x‖ ≤ ‖T‖ ^ n * ‖x‖ := op_norm_pow_apply_le T n x
    _ ≤ c ^ n * ‖x‖ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg T) h n)
        (norm_nonneg x)

/-! ## 距离与 Lipschitz -/

/-- 线性算子是全局 `‖T‖`-Lipschitz：`‖T x - T y‖ ≤ ‖T‖ ‖x - y‖`。 -/
theorem op_dist_le (T : E →L[ℝ] F) (x y : E) : ‖T x - T y‖ ≤ ‖T‖ * ‖x - y‖ := by
  rw [← map_sub]
  exact T.le_opNorm (x - y)

/-- 深层距离界：`‖T^n x - T^n y‖ ≤ ‖T‖^n ‖x - y‖`。 -/
theorem op_dist_pow_le (T : E →L[ℝ] E) (n : ℕ) (x y : E) :
    ‖(T ^ n) x - (T ^ n) y‖ ≤ ‖T‖ ^ n * ‖x - y‖ := by
  rw [← map_sub]
  exact op_norm_pow_apply_le T n (x - y)

end Lattice
