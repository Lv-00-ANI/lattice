import Mathlib
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: 实对称矩阵有限维谱定理（回收 mathlib）

本文件把 mathlib 4.14 的 **Hermitian 矩阵谱定理**（`Matrix.IsHermitian.spectral_theorem`
与 `Matrix.IsHermitian.star_mul_self_mul_eq_diagonal`）回收到 ℝ 上的**实对称矩阵**情形，
给出「正交对角化」的完整、可直接使用的形式：

  1. `real_conjTranspose_eq_transpose`：ℝ 上共轭转置 = 转置；
  2. `real_isHermitian_iff_transpose`：`A.IsHermitian ↔ Aᵀ = A`；
  3. `symmetric_eigenpair`：每个特征向量基向量满足 `A *ᵥ vᵢ = λᵢ • vᵢ`；
  4. `symmetric_orthonormal_eigenbasis` / `symmetric_eigenvector_inner`：
     `hA.eigenvectorBasis` 是标准正交基，内积为 Kronecker δ；
  5. `symmetric_spectral_theorem_eigen` / `symmetric_spectral_theorem`：
     `A = U · diag λ · Uᵀ` 且 `Uᵀ U = 1`（正交矩阵，`U Uᵀ = 1` 已导出）；
  6. `symmetric_det_eq_prod_eigenvalues` / `symmetric_two_two_det`：
     `det A = ∏ λᵢ`，2×2 特例 `det A = λ₀ λ₁`；
  7. `symmetric_trace_eq_sum_eigenvalues`：`trace A = ∑ λᵢ`；
  8. n = 1 特例：`A = A₀₀ • 1`，`A₀₀` 是实特征值，`‖A‖_F = |A₀₀|`；
  9. `sum_sq_eq_trace_transpose_mul`、`trace_mul_self_conj`、
     `symmetric_frobenius_eq_sum_eigenvalues_sq`：
     `∑ᵢⱼ Aᵢⱼ² = ∑ᵢ λᵢ²`（Frobenius 平方 = 特征值平方和）。

## 诚实标注与降级（诚实 / 未证 / 未做 / 降级 / 标注）

· 本文件**回收** mathlib 的 Hermitian 谱定理，不重新证明谱定理本身（诚实）；
· **一般（非对称）矩阵的 SVD（奇异值分解）未构造、未做**：mathlib 4.14 不提供任意实
  矩阵的 SVD；本文件只处理 `Aᵀ = A` 的方阵（未做）；
· 复谱 / 非实特征值不在范围：实对称矩阵的特征值必为实数，故这里没有「降级」缺口，
  但一般实矩阵可能只有复特征值，本文件**不声称**（标注）；
· 特征值的**排序**由 mathlib 内部选择决定；本文件只使用与排序无关（多重集）的结论
  `det = ∏ λ`、`trace = ∑ λ`、`∑ λ²`，不断言任何单调性或逐点排序（标注）；
· `symmetric_spectral_theorem` 的正交性只要求 `Uᵀ U = 1`；另一方向 `U Uᵀ = 1` 由
  `Matrix.mul_eq_one_comm` 导出，可分别使用（降级：不把它塞进存在量词以免使用不便）。
-/

noncomputable section

open scoped InnerProduct
open scoped Matrix

namespace Lattice

open Matrix
open scoped BigOperators

variable {n : ℕ}

/-! ## 一、ℝ 上 Hermitian ↔ 对称 -/

/-- ℝ 上矩阵的共轭转置 = 转置（`star` 在 ℝ 上是恒等）。 -/
theorem real_conjTranspose_eq_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Aᴴ = Aᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- 实方阵 Hermitian 当且仅当对称。 -/
theorem real_isHermitian_iff_transpose (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsHermitian ↔ Aᵀ = A := by
  unfold Matrix.IsHermitian
  rw [real_conjTranspose_eq_transpose A]

/-! ## 二、特征对与标准正交特征基 -/

/-- 谱定理的逐特征对形式：`A *ᵥ vᵢ = λᵢ • vᵢ`。 -/
theorem symmetric_eigenpair (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (i : Fin n) :
    A *ᵥ ⇑(hA.eigenvectorBasis i) = hA.eigenvalues i • ⇑(hA.eigenvectorBasis i) :=
  hA.mulVec_eigenvectorBasis i

/-- 特征向量基是标准正交基（回收 `OrthonormalBasis.orthonormal`）。 -/
theorem symmetric_orthonormal_eigenbasis (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Orthonormal ℝ (⇑(hA.eigenvectorBasis)) :=
  hA.eigenvectorBasis.orthonormal

/-- 特征向量基的内积 = Kronecker δ。 -/
theorem symmetric_eigenvector_inner (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (i j : Fin n) :
    (inner (hA.eigenvectorBasis i) (hA.eigenvectorBasis j) : ℝ) =
      if i = j then 1 else 0 :=
  (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j

/-! ## 三、正交对角化（谱定理的实形式） -/

/-- 实谱定理（具体见证）：用 `hA.eigenvectorUnitary` 与 `hA.eigenvalues` 直接写出
`A = U · diag λ · Uᵀ`。 -/
theorem symmetric_spectral_theorem_eigen (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) * diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  have h := hA.spectral_theorem
  rw [Matrix.star_eq_conjTranspose, real_conjTranspose_eq_transpose] at h
  have hD : diagonal (RCLike.ofReal ∘ hA.eigenvalues) = diagonal hA.eigenvalues := by
    simp [RCLike.ofReal_real_eq_id]
  rwa [hD] at h

/-- `hA.eigenvectorUnitary` 的正交性：`Uᵀ U = 1`。 -/
theorem symmetric_eigenvectorUnitary_transpose_mul (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (hA.eigenvectorUnitary).2
  rwa [Matrix.star_eq_conjTranspose, real_conjTranspose_eq_transpose] at h

/-- `hA.eigenvectorUnitary` 的正交性（另一方向）：`U Uᵀ = 1`（由 `mul_eq_one_comm` 导出）。 -/
theorem symmetric_eigenvectorUnitary_mul_transpose (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm).mp (symmetric_eigenvectorUnitary_transpose_mul A hA)

/-- **实谱定理（存在形式）**：存在正交矩阵 `U` 与实向量 `lam`，
使 `Uᵀ U = 1` 且 `A = U · diag lam · Uᵀ`。 -/
theorem symmetric_spectral_theorem (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ),
      Uᵀ * U = 1 ∧ A = U * diagonal lam * Uᵀ :=
  ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), hA.eigenvalues,
    symmetric_eigenvectorUnitary_transpose_mul A hA, symmetric_spectral_theorem_eigen A hA⟩

/-! ## 四、行列式 / 迹 = 特征值的（对称）函数 -/

/-- 实对称矩阵的行列式 = 特征值之积。 -/
theorem symmetric_det_eq_prod_eigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    A.det = ∏ i, hA.eigenvalues i := by
  simpa using hA.det_eq_prod_eigenvalues

/-- 实对称矩阵的迹 = 特征值之和（由谱定理 + 迹的循环性）。 -/
theorem symmetric_trace_eq_sum_eigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Matrix.trace A = ∑ i, hA.eigenvalues i := by
  have h := congr_arg Matrix.trace (hA.star_mul_self_mul_eq_diagonal)
  rw [Matrix.trace_mul_cycle] at h
  have hunit : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_unitaryGroup_iff).mp (hA.eigenvectorUnitary).2
  rw [hunit, Matrix.one_mul] at h
  rw [h, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]

/-- 2×2 特例：`det A = λ₀ · λ₁`。 -/
theorem symmetric_two_two_det (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsHermitian) :
    A.det = hA.eigenvalues 0 * hA.eigenvalues 1 := by
  rw [symmetric_det_eq_prod_eigenvalues A hA, Fin.prod_univ_two]

/-- 2×2 特例：`trace A = λ₀ + λ₁`。 -/
theorem symmetric_two_two_trace (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsHermitian) :
    Matrix.trace A = hA.eigenvalues 0 + hA.eigenvalues 1 := by
  rw [symmetric_trace_eq_sum_eigenvalues A hA, Fin.sum_univ_two]

/-! ## 五、n = 1 特例 -/

/-- n = 1 特例：`A = A₀₀ • 1`。 -/
theorem symmetric_one_one_eq_smul (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A = A 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- n = 1 特例：`A 0 0` 是实特征值（存在非零实特征向量）。 -/
theorem symmetric_one_one_eigenvector (A : Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ v : EuclideanSpace ℝ (Fin 1), v ≠ 0 ∧ A *ᵥ v = (A 0 0) • v := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have h0 := congr_fun h 0
    simp at h0
  · ext i
    fin_cases i
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_one]

/-- n = 1 特例：Frobenius 范数 = `|A 0 0|`。 -/
theorem frobeniusNorm_one_one (A : Matrix (Fin 1) (Fin 1) ℝ) :
    frobeniusNorm A = |A 0 0| := by
  unfold frobeniusNorm
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  exact Real.sqrt_sq_eq_abs _

/-! ## 六、Frobenius 平方 = 特征值平方和 -/

/-- `∑ᵢⱼ Aᵢⱼ² = trace (Aᵀ A)`（矩形矩阵亦成立）。 -/
theorem sum_sq_eq_trace_transpose_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) = Matrix.trace (Aᵀ * A) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- 正交相似下 `(U D Uᵀ)²` 的迹 = `D²` 的迹（只需 `Uᵀ U = 1`）。 -/
theorem trace_mul_self_conj (U D : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) :
    Matrix.trace ((U * D * Uᵀ) * (U * D * Uᵀ)) = Matrix.trace (D * D) := by
  have hAA : (U * D * Uᵀ) * (U * D * Uᵀ) = U * (D * D) * Uᵀ := by
    calc (U * D * Uᵀ) * (U * D * Uᵀ)
        = U * (D * (Uᵀ * (U * (D * Uᵀ)))) := by simp only [Matrix.mul_assoc]
      _ = U * (D * ((Uᵀ * U) * (D * Uᵀ))) := by rw [← Matrix.mul_assoc Uᵀ U (D * Uᵀ)]
      _ = U * (D * (1 * (D * Uᵀ))) := by rw [hU]
      _ = U * (D * (D * Uᵀ)) := by rw [Matrix.one_mul]
      _ = U * (D * D) * Uᵀ := by simp only [Matrix.mul_assoc]
  rw [hAA, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- 若 `A = U D Uᵀ` 且 `Uᵀ U = 1`，则 `trace (A A) = trace (D D)`。
（单独陈述以避免在含 `hA` 的语境中重写 `A` 造成的依赖性问题。） -/
theorem trace_mul_self_conj_of_decomp (A U D : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (h : A = U * D * Uᵀ) : Matrix.trace (A * A) = Matrix.trace (D * D) := by
  rw [h]
  exact trace_mul_self_conj U D hU

/-- **实对称矩阵的 Frobenius 平方 = 特征值平方和**：
`∑ᵢⱼ Aᵢⱼ² = ∑ᵢ λᵢ²`。 -/
theorem symmetric_frobenius_eq_sum_eigenvalues_sq (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) = ∑ i, (hA.eigenvalues i) ^ 2 := by
  have hAt : Aᵀ = A := (real_isHermitian_iff_transpose A).mp hA
  have hU := symmetric_eigenvectorUnitary_transpose_mul A hA
  calc (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)
      = Matrix.trace (Aᵀ * A) := sum_sq_eq_trace_transpose_mul A
    _ = Matrix.trace (A * A) := by rw [hAt]
    _ = Matrix.trace (diagonal hA.eigenvalues * diagonal hA.eigenvalues) :=
          trace_mul_self_conj_of_decomp A _ _ hU (symmetric_spectral_theorem_eigen A hA)
    _ = Matrix.trace (diagonal fun i => hA.eigenvalues i * hA.eigenvalues i) := by
          rw [Matrix.diagonal_mul_diagonal]
    _ = ∑ i, (hA.eigenvalues i) ^ 2 := by
          rw [Matrix.trace_diagonal]
          apply Finset.sum_congr rfl
          intro i _
          ring

end Lattice
