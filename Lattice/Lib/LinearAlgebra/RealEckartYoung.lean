import Mathlib
import Lattice.Lib.Architectures.RealTensorNorm
import Lattice.Lib.LinearAlgebra.RealLowRank
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.LinearAlgebra.RealSVD
/-!
# LATTICE: Eckart–Young–Mirsky 的诚实降级（奇异值框架 + 精确情形 + 下界）

本文件在 `RealSVD` 的实对称谱定理之上，为**任意实矩阵** `A : Matrix (Fin m) (Fin n) ℝ`
建立**奇异值平方**的严格定义与可证性质，并给出 Eckart–Young–Mirsky（EYM）最优性的
**诚实降级**版本。

## 内容

  1. `gramIsHermitian`：Gram 矩阵 `Aᵀ A : Matrix (Fin n) (Fin n) ℝ` 是 Hermitian（实对称）；
  2. `singularValueSq`：奇异值**平方** `σᵢ² := (Aᵀ A) 的第 i 个特征值`；
  3. `singularValue`：奇异值 `σᵢ := √(σᵢ²)`；`singularValue_nonneg`、`singularValue_sq`；
  4. `tailSingularValueSq`：尾部平方和 `∑_{i > k} σᵢ²`；`tailSingularValueSq_nonneg`、
     `tailSingularValueSq_le_total`（尾部 ≤ 全体，仅用非负性即可）；
  5. `frobenius_sq_eq_sum_singularValueSq`：`∑ᵢ σᵢ² = ‖A‖_F²`
     （由 `RealSVD.sum_sq_eq_trace_transpose_mul` + `RealSVD.symmetric_trace_eq_sum_eigenvalues`）；
  6. 可证的下界 / 精确情形（EYM 的诚实替代）：
     · `frobeniusNorm_nonneg_error`：`0 ≤ ‖A − B‖_F`；
     · `rankZero_exact`：`‖A − 0‖_F = ‖A‖_F`（k = 0 的**精确情形**）；
     · `eym_lower_bound_triangle`：`‖A − B‖_F ≥ ‖A‖_F − ‖B‖_F`（Frobenius 三角不等式）；
     · `bestApprox_self`：`‖A − A‖_F = 0`（误差非负且可达 0）。

## **Eckart–Young–Mirsky 最优性未证/未做（降级）**

完整证明需要奇异值分解的截断构造 `A_k`，mathlib 4.14 未提供；因此本文件**不声称**
`‖A − A_k‖_F = √(∑_{i>k} σᵢ²)` 的**最优性（等式方向）**。本文件提供：
(a) 由 `AᵀA` 的实谱定理严格定义的奇异值平方 `σᵢ²`（非负性已证）；
(b) k = 0 的精确情形；
(c) 三角不等式下界；
(d) 尾部 `σ²` 和 ≤ 全部 `σ²` 和。
**明确缺口**：任何 `rank B ≤ k` 的 `B` 满足 `‖A − B‖_F ≥ √(∑_{i>k} σᵢ²)` 这一步**未证**，
最优性只在所获得的谱信息下成立（标注）。

另：`RealLowRank` 中已有的诚实标注（其 `frob` 为 `m → n → ℝ` 表示，与 `Matrix` 定义等价）
继续有效；本文件不修改 `RealLowRank`，仅引用其 Frobenius 三角不等式
（`RealLowRank` 模块中的 `Lattice.frob_add_le`，本文件内直接写 `frob_add_le`）。**无 sorry / axiom / admit。**
-/

noncomputable section

open scoped InnerProduct
open scoped Matrix

namespace Lattice

open Matrix
open scoped BigOperators

variable {m n : ℕ}

/-! ## 一、Gram 矩阵与奇异值平方 -/

/-- Gram 矩阵 `Aᵀ A`（`n × n`）是 Hermitian（ℝ 上即对称）。 -/
def gramIsHermitian (A : Matrix (Fin m) (Fin n) ℝ) : (Aᵀ * A).IsHermitian :=
  Matrix.isHermitian_transpose_mul_self A

/-- 奇异值**平方** `σᵢ²`：`Aᵀ A` 的第 `i` 个特征值。 -/
def singularValueSq (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) : ℝ :=
  (gramIsHermitian A).eigenvalues i

/-- 奇异值平方非负（由 `Aᵀ A` 半正定）。 -/
theorem singularValueSq_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    0 ≤ singularValueSq A i := by
  unfold singularValueSq gramIsHermitian
  exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i

/-- 奇异值 `σᵢ := √(σᵢ²)`。 -/
def singularValue (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (singularValueSq A i)

/-- 奇异值非负。 -/
theorem singularValue_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    0 ≤ singularValue A i :=
  Real.sqrt_nonneg _

/-- 奇异值的平方回原：`σᵢ² = σᵢ²`（开方后平方）。 -/
theorem singularValue_sq (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    singularValue A i ^ 2 = singularValueSq A i :=
  Real.sq_sqrt (singularValueSq_nonneg A i)

/-! ## 二、尾部奇异值平方和 -/

/-- 尾部平方和 `∑_{i > k} σᵢ²`（截断误差的谱量；此处仅作定义）。 -/
def tailSingularValueSq (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ i in (Finset.univ.filter (fun i : Fin n => k < i.val)), singularValueSq A i

/-- 尾部平方和非负。 -/
theorem tailSingularValueSq_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    0 ≤ tailSingularValueSq A k := by
  unfold tailSingularValueSq
  exact Finset.sum_nonneg (fun i _ => singularValueSq_nonneg A i)

/-- 尾部平方和 ≤ 全部平方和（仅用非负性）。 -/
theorem tailSingularValueSq_le_total (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    tailSingularValueSq A k ≤ ∑ i : Fin n, singularValueSq A i := by
  unfold tailSingularValueSq
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => singularValueSq_nonneg A i)

/-! ## 三、奇异值平方和 = Frobenius 范数平方 -/

/-- **`∑ᵢ σᵢ² = ‖A‖_F²`**：全部奇异值平方和等于 Frobenius 范数平方。 -/
theorem frobenius_sq_eq_sum_singularValueSq (A : Matrix (Fin m) (Fin n) ℝ) :
    (∑ i : Fin n, singularValueSq A i) = frobeniusNorm A ^ 2 := by
  have h1 : Matrix.trace (Aᵀ * A) = ∑ i : Fin n, singularValueSq A i :=
    symmetric_trace_eq_sum_eigenvalues (Aᵀ * A) (gramIsHermitian A)
  rw [← h1, ← sum_sq_eq_trace_transpose_mul A, frobeniusNorm_sq]

/-! ## 四、EYM 的诚实替代：精确情形与下界 -/

/-- 误差的 Frobenius 范数非负（最优误差非负的下界性）。 -/
theorem frobeniusNorm_nonneg_error (A B : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusNorm (A - B) :=
  frobeniusNorm_nonneg _

/-- **k = 0 的精确情形**：零矩阵是精确近似，`‖A − 0‖_F = ‖A‖_F`。 -/
theorem rankZero_exact (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (A - 0) = frobeniusNorm A := by
  rw [sub_zero]

/-- **三角不等式下界**：`‖A − B‖_F ≥ ‖A‖_F − ‖B‖_F`
（由 Frobenius 三角不等式 `RealLowRank.frob_add_le` 导出）。 -/
theorem eym_lower_bound_triangle (A B : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (A - B) ≥ frobeniusNorm A - frobeniusNorm B := by
  have h0 : frobeniusNorm A ≤ frobeniusNorm (A - B) + frobeniusNorm B := by
    have h := frob_add_le (m := Fin m) (n := Fin n) (A - B) B
    rw [sub_add_cancel] at h
    exact h
  linarith

/-- 自近似误差为 0：`B = A` 时 `‖A − A‖_F = 0`（配合非负性即最小可能误差）。 -/
theorem bestApprox_self (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (A - A) = 0 := by
  simp [frobeniusNorm]

end Lattice
