import Mathlib

/-!
# LATTICE: Fin 矩阵完整算子范数 —— 次乘法性 / Frobenius↔算子范数双向界 / 转置衔接

VERIFICATION.md §5「维度」展望的实现：Fin 矩阵的**完整算子范数**理论。
以 `RealMatrix.matvec`（行点积）与 `RealOperatorNorm`（算子范数代数：
`opNorm_comp_le`/`le_opNorm` 等）为基础，把矩阵作为**欧氏空间**上的连续
线性算子（`matCLME` 桥）研究：

  1. 次乘法性：‖A·B‖_op ≤ ‖A‖_op·‖B‖_op —— 矩阵乘法 = 线性映射复合
     （`matvecE_mul`：逐元素展开 + `Matrix.mulVec_mulVec`），复合范数
     用 `ContinuousLinearMap.opNorm_comp_le` 组装；
  2. Frobenius 界算子：‖A‖_op ≤ ‖A‖_F —— 经 Cauchy-Schwarz
     （`abs_real_inner_le_norm`：行向量与 x 的欧氏内积）得逐点界
     ‖Ax‖ ≤ ‖A‖_F·‖x‖，由 `LinearMap.mkContinuous` 构造连续线性映射
     并读其范数界（`LinearMap.mkContinuous_norm_le`）；
  3. 反向：‖A‖_F ≤ √n·‖A‖_op（n = 列数）—— 把 Frobenius 平方分解为
     各列 ‖A·eⱼ‖² 之和（`frobenius_sq_eq_sum_col`），逐列
     ‖A eⱼ‖ ≤ ‖A‖_op·‖eⱼ‖（`le_opNorm`，‖eⱼ‖ = 1），平方后开方；
  4. 转置衔接：‖Aᵀ‖_op = ‖A‖_op —— 转置是伴随：内积对偶
     ⟪Ax, y⟫ = ⟪x, Aᵀy⟫（`matvecE_adjoint_eq`，求和交换），配合
     `ContinuousLinearMap.adjoint` 保范数（`norm_map`）。

矩阵尺寸约定：`A : Matrix (Fin m) (Fin n) ℝ`（m 行 n 列）作用于
`EuclideanSpace ℝ (Fin n)`，值在 `EuclideanSpace ℝ (Fin m)`（欧氏 2-范数）。
Frobenius 范数 = ‖A‖_F = √(Σᵢ Σⱼ Aᵢⱼ²)（自定义，mathlib 无现成定义）。

模型无关：任意 m×n 维度（Fin 指标）；无 sorry/axiom/admit。
-/

noncomputable section

open scoped InnerProduct

namespace Lattice

open Matrix
open scoped BigOperators

variable {l m n : ℕ}

/-! ## Frobenius 范数（自定义）与欧氏范数工具 -/

/-- Frobenius 范数：‖A‖_F = √(Σᵢ Σⱼ Aᵢⱼ²)（ℝ 上 Aᵢⱼ² = ‖Aᵢⱼ‖²）。 -/
def frobeniusNorm (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2)

lemma frobeniusNorm_nonneg (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobeniusNorm A := by
  unfold frobeniusNorm
  exact Real.sqrt_nonneg _

/-- 平方和 Σᵢ Σⱼ Aᵢⱼ² ≥ 0（开方前提）。 -/
lemma sum_sq_nonneg {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℝ) :
    0 ≤ ∑ i : Fin k, ∑ j : Fin l, (A i j) ^ 2 := by
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg _))

/-- 欧氏范数平方 = 逐坐标平方和：‖x‖² = Σⱼ xⱼ²。 -/
lemma euclid_norm_sq_eq {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    ‖x‖ ^ 2 = ∑ j : Fin k, (x j) ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Real.norm_eq_abs, sq_abs]
  · positivity

/-! ## 欧氏矩阵-向量乘法（行点积）与线性性 -/

/-- 矩阵乘欧氏向量（行点积）：(Ax)ᵢ = Σⱼ Aᵢⱼ xⱼ。 -/
def matvecE (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  fun i : Fin m => ∑ j : Fin n, A i j * x j

lemma matvecE_add (A : Matrix (Fin m) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    matvecE A (x + y) = matvecE A x + matvecE A y := by
  ext i
  unfold matvecE
  calc
    (∑ j : Fin n, A i j * (x j + y j)) = ∑ j : Fin n, (A i j * x j + A i j * y j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j : Fin n, A i j * x j) + (∑ j : Fin n, A i j * y j) := by
      rw [Finset.sum_add_distrib]

lemma matvecE_smul (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matvecE A (c • x) = c • matvecE A x := by
  ext i
  unfold matvecE
  calc
    (∑ j : Fin n, A i j * (c * x j)) = ∑ j : Fin n, c * (A i j * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ j : Fin n, A i j * x j := by
      rw [Finset.mul_sum]

/-- 矩阵乘法 = 线性映射复合：(A·B)x = A(Bx)（`mulVec_mulVec`）。 -/
lemma matvecE_mul (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    matvecE (A * B) x = matvecE A (matvecE B x) := by
  change Matrix.mulVec (A * B) x = Matrix.mulVec A (Matrix.mulVec B x)
  exact (Matrix.mulVec_mulVec (v := x) (M := A) (N := B)).symm

/-- 单位向量作用：A·eⱼ = A 的第 j 列（eⱼ = `EuclideanSpace.single j 1`）。 -/
lemma matvecE_single (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    matvecE A (EuclideanSpace.single j (1 : ℝ)) = fun i : Fin m => A i j := by
  ext i
  unfold matvecE
  calc
    (∑ j_1 : Fin n, A i j_1 * EuclideanSpace.single j (1 : ℝ) j_1) = A i j * 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b hb hbj
        rw [EuclideanSpace.single_apply, if_neg hbj]
        simp
      · intro hj
        simp at hj
    _ = A i j := by ring

/-! ## Cauchy-Schwarz：Frobenius 界算子范数（行向量 × x） -/

/-- 行 Cauchy-Schwarz：内积 ⟪Aᵢ·, x⟫ = Σⱼ Aᵢⱼ xⱼ 满足
(Σⱼ Aᵢⱼ xⱼ)² ≤ (Σⱼ Aᵢⱼ²)·(Σⱼ xⱼ²)。 -/
lemma row_cs_bound (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    (∑ j : Fin n, A i j * x j) ^ 2 ≤ (∑ j : Fin n, (A i j) ^ 2) * (∑ j : Fin n, (x j) ^ 2) := by
  let u : EuclideanSpace ℝ (Fin n) := fun j : Fin n => A i j
  have hcs := abs_real_inner_le_norm u x
  have hsq : (inner u x) ^ 2 ≤ ‖u‖ ^ 2 * ‖x‖ ^ 2 := by
    calc
      (inner u x) ^ 2 = |(inner u x)| ^ 2 := by rw [sq_abs]
      _ ≤ (‖u‖ * ‖x‖) ^ 2 := by
        have hb : 0 ≤ ‖u‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hb] using hcs)
      _ = ‖u‖ ^ 2 * ‖x‖ ^ 2 := by ring
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hsq
  rw [euclid_norm_sq_eq, euclid_norm_sq_eq] at hsq
  simpa [Matrix.dotProduct, u] using hsq

/-! ## Frobenius 范数平方的两种展开 -/

lemma frobeniusNorm_sq (A : Matrix (Fin m) (Fin n) ℝ) :
    (frobeniusNorm A) ^ 2 = ∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2 := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt (sum_sq_nonneg A)]

/-- 逐点界：‖Ax‖ ≤ ‖A‖_F·‖x‖（行 CS 逐行 + 求和 + 开方）。 -/
lemma frobenius_bound (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖matvecE A x‖ ≤ frobeniusNorm A * ‖x‖ := by
  have hsq : ‖matvecE A x‖ ^ 2 ≤ (frobeniusNorm A * ‖x‖) ^ 2 := by
    calc
      ‖matvecE A x‖ ^ 2 = ∑ i : Fin m, (matvecE A x i) ^ 2 := by rw [euclid_norm_sq_eq]
      _ = ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ ≤ ∑ i : Fin m, ((∑ j : Fin n, (A i j) ^ 2) * (∑ j : Fin n, (x j) ^ 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact row_cs_bound A x i
      _ = (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) * (∑ j : Fin n, (x j) ^ 2) := by
        rw [← Finset.sum_mul]
      _ = (frobeniusNorm A) ^ 2 * ‖x‖ ^ 2 := by
        rw [← frobeniusNorm_sq]
        rw [← euclid_norm_sq_eq]
      _ = (frobeniusNorm A * ‖x‖) ^ 2 := by ring
  have ha : 0 ≤ ‖matvecE A x‖ := norm_nonneg _
  have hb : 0 ≤ frobeniusNorm A * ‖x‖ := mul_nonneg (frobeniusNorm_nonneg A) (norm_nonneg _)
  have habs : |‖matvecE A x‖| ≤ |frobeniusNorm A * ‖x‖| := (sq_le_sq.mp hsq)
  simpa [abs_of_nonneg ha, abs_of_nonneg hb] using habs

/-! ## 矩阵 → 欧氏连续线性算子（桥） -/

def matvecELin (A : Matrix (Fin m) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun := matvecE A
  map_add' := matvecE_add A
  map_smul' := matvecE_smul A

/-- 矩阵作为欧氏空间上的连续线性算子（以 ‖A‖_F 为显式界构造）。 -/
def matCLME (A : Matrix (Fin m) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (matvecELin A).mkContinuous (frobeniusNorm A) (frobenius_bound A)

lemma matCLME_apply (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matCLME A x = matvecE A x := by
  unfold matCLME
  rw [LinearMap.mkContinuous_apply]
  rfl

/-! ## 定理二：Frobenius 界算子范数 ‖A‖_op ≤ ‖A‖_F -/

theorem opNorm_le_frobenius (A : Matrix (Fin m) (Fin n) ℝ) : ‖matCLME A‖ ≤ frobeniusNorm A := by
  unfold matCLME
  exact LinearMap.mkContinuous_norm_le (matvecELin A) (frobeniusNorm_nonneg A) (frobenius_bound A)

/-! ## 定理一：次乘法性 ‖A·B‖_op ≤ ‖A‖_op·‖B‖_op -/

lemma matCLME_mul (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    matCLME (A * B) = matCLME A ∘L matCLME B := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  rw [matCLME_apply]
  rw [matCLME_apply]
  rw [matCLME_apply]
  exact matvecE_mul A B x

theorem matrix_mul_norm_bound (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    ‖matCLME (A * B)‖ ≤ ‖matCLME A‖ * ‖matCLME B‖ := by
  rw [matCLME_mul]
  exact (matCLME A).opNorm_comp_le (matCLME B)

/-! ## 定理三：反向 ‖A‖_F ≤ √n·‖A‖_op（逐列分解） -/

lemma col_norm_sq (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    ‖matvecE A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 = ∑ i : Fin m, (A i j) ^ 2 := by
  rw [euclid_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [matvecE_single]

lemma col_norm_le_opNorm (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    ‖matvecE A (EuclideanSpace.single j (1 : ℝ))‖ ≤ ‖matCLME A‖ := by
  have h := (matCLME A).le_opNorm (EuclideanSpace.single j (1 : ℝ))
  rw [matCLME_apply] at h
  rw [EuclideanSpace.norm_single] at h
  simpa using h

/-- Frobenius 平方 = 各列范数平方之和。 -/
lemma frobenius_sq_eq_sum_col (A : Matrix (Fin m) (Fin n) ℝ) :
    (frobeniusNorm A) ^ 2 = ∑ j : Fin n, ‖matvecE A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  rw [frobeniusNorm_sq]
  calc
    (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) = ∑ j : Fin n, ∑ i : Fin m, (A i j) ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ‖matvecE A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [col_norm_sq]

/-- 诚实反向界：‖A‖_F ≤ √n·‖A‖_op（n = 列数；标准形式为 √n，未强求 √(m·n)）。 -/
theorem frobenius_le_opNorm_sqrt (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ≤ Real.sqrt (n : ℝ) * ‖matCLME A‖ := by
  have hsq : (frobeniusNorm A) ^ 2 ≤ (n : ℝ) * ‖matCLME A‖ ^ 2 := by
    calc
      (frobeniusNorm A) ^ 2 = ∑ j : Fin n, ‖matvecE A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        frobenius_sq_eq_sum_col A
      _ ≤ ∑ j : Fin n, ‖matCLME A‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hle := col_norm_le_opNorm A j
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
          exact hle)
      _ = (Fintype.card (Fin n)) * ‖matCLME A‖ ^ 2 := by
        simp
      _ = (n : ℝ) * ‖matCLME A‖ ^ 2 := by
        simp [Fintype.card_fin]
  have hsqrt : (Real.sqrt (n : ℝ) * ‖matCLME A‖) ^ 2 = (n : ℝ) * ‖matCLME A‖ ^ 2 := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    rw [mul_pow, Real.sq_sqrt hn]
  have hsq' : (frobeniusNorm A) ^ 2 ≤ (Real.sqrt (n : ℝ) * ‖matCLME A‖) ^ 2 := by
    rwa [hsqrt]
  have hnonneg : 0 ≤ Real.sqrt (n : ℝ) * ‖matCLME A‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have habs : |frobeniusNorm A| ≤ |Real.sqrt (n : ℝ) * ‖matCLME A‖| := (sq_le_sq.mp hsq')
  simpa [abs_of_nonneg (frobeniusNorm_nonneg A), abs_of_nonneg hnonneg] using habs

/-! ## 定理四：转置衔接 ‖Aᵀ‖_op = ‖A‖_op（转置 = 伴随） -/

/-- 内积对偶：⟪Ax, y⟫ = ⟪x, Aᵀy⟫（转置是伴随；求和交换）。 -/
lemma matvecE_adjoint_eq (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    (inner (matvecE A x) y : ℝ) = (inner x (matvecE Aᵀ y) : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.dotProduct, matvecE, Matrix.transpose_apply]
  calc
    (∑ i : Fin m, (∑ j : Fin n, A i j * x j) * y i)
        = ∑ i : Fin m, ∑ j : Fin n, (A i j * x j) * y i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ i : Fin m, (A i j * x j) * y i := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, x j * (∑ i : Fin m, A i j * y i) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            (∑ i : Fin m, (A i j * x j) * y i) = ∑ i : Fin m, x j * (A i j * y i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = x j * (∑ i : Fin m, A i j * y i) := by
              rw [Finset.mul_sum]

/-- 单位基向量取坐标：vⱼ = ⟪eⱼ, v⟫（ℝ 上 conj 1 = 1）。 -/
lemma basis_coord (v : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    v j = inner (EuclideanSpace.single j (1 : ℝ)) v := by
  rw [EuclideanSpace.inner_single_left]
  simp

/-- 转置是伴随：matCLME Aᵀ = (matCLME A)†。 -/
lemma matCLME_adjoint (A : Matrix (Fin m) (Fin n) ℝ) :
    (matCLME A)† = matCLME Aᵀ := by
  apply ContinuousLinearMap.ext
  intro y
  ext j
  calc
    (ContinuousLinearMap.adjoint (matCLME A) y) j
        = inner (EuclideanSpace.single j (1 : ℝ)) (ContinuousLinearMap.adjoint (matCLME A) y) := by
      rw [EuclideanSpace.inner_single_left]
      simp
    _ = inner (matCLME A (EuclideanSpace.single j (1 : ℝ))) y := by
      exact ContinuousLinearMap.adjoint_inner_right (matCLME A) (EuclideanSpace.single j (1 : ℝ)) y
    _ = inner (EuclideanSpace.single j (1 : ℝ)) (matCLME Aᵀ y) := by
      rw [matCLME_apply, matCLME_apply]
      exact matvecE_adjoint_eq A (EuclideanSpace.single j (1 : ℝ)) y
    _ = (matCLME Aᵀ y) j := by
      rw [EuclideanSpace.inner_single_left]
      simp

/-- 转置保算子范数：‖Aᵀ‖_op = ‖A‖_op（伴随保范数）。 -/
theorem norm_transpose_eq (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖matCLME Aᵀ‖ = ‖matCLME A‖ := by
  rw [← matCLME_adjoint A]
  exact (ContinuousLinearMap.adjoint.norm_map (matCLME A))

end Lattice
