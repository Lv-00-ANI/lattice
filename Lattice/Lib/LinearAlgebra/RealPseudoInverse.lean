import Mathlib
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: Moore–Penrose 伪逆（初等构造版）—— A⁺ = (AᵀA)⁻¹Aᵀ 的四条 Penrose 等式

mathlib 4.14 **没有**一般矩阵的 Moore–Penrose 伪逆 API（SVD 亦无），
故此处取**满列秩**情形下的标准显式构造

  `pseudoInverse A = (AᵀA)⁻¹ · Aᵀ`（假设 AᵀA 可逆，等价于 A 列满秩），

并对该构造给出**完整可证**的 Moore–Penrose 性质与最小二乘理论：

  1. `pseudoInverse_penrose_eq1`：A A⁺ A = A；
  2. `pseudoInverse_penrose_eq2`：A⁺ A A⁺ = A⁺；
  3. `pseudoInverse_penrose_eq3`：(A A⁺)ᵀ = A A⁺（A A⁺ 自伴）；
  4. `pseudoInverse_penrose_eq4`：(A⁺ A)ᵀ = A⁺ A，且更强地 A⁺ A = 1；
  5. `normal_equation_of_pseudoInverse`：x = A⁺b 满足法方程 AᵀA x = Aᵀb；
  6. `pseudoInverse_leastSquares_optimal`：x = A⁺b 是**全局**最小二乘解
     （A y − b = A(y − x) + (A x − b)，交叉项由伴随性与法方程归零）；
  7. `normal_equation_unique`：AᵀA 可逆 ⟹ 法方程解唯一；
  8. `projection_onto_range`：A A⁺ 是到 range A 的**正交投影**
     —— 自伴（eq3）+ 幂等 + 固定 range A。自伴 + 幂等正是正交投影的
     标准刻画，故此处以这三条代数性质代替「内积正交性」的显式叙述。

诚实假设与降级（明确标注）：
  · 完整 Penrose 定理（对**任意**矩阵存在唯一 A⁺ 满足四条等式）依赖
    SVD / 特征分解，mathlib 4.14 无此 API，**本文件不声称**该结论；
  · 本文件构造只要求 `IsUnit (AᵀA).det` 这一条代数条件；在本文件的 ℝ
    取值下 `IsUnit (AᵀA).det` ⟺ A 列满秩（列满秩是该条件的等价刻画，
    而非构造本身的前提），此时 A⁺ 是
    A 的左逆型伪逆（A⁺A = 1）；
  · `pseudoInverse_leastSquares_optimal` 的全局最优性在此直接证明
    （作为 NormSqLoss 意义上 ‖A y − b‖² 的最小值），无需一致系统假设。

模型无关：任意 `Fin` 维度 m×n。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

open Matrix
open scoped BigOperators

variable {m n : ℕ}

/-! ## 定义：法方程矩阵与伪逆 -/

/-- 法方程矩阵：AᵀA（n×n）。 -/
def normalMatrix (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := Aᵀ * A

/-- 伪逆（满列秩构造）：A⁺ = (AᵀA)⁻¹·Aᵀ（n×m）。 -/
def pseudoInverse (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  (normalMatrix A)⁻¹ * Aᵀ

/-- AᵀA 对称。 -/
lemma normalMatrix_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    (normalMatrix A)ᵀ = normalMatrix A := by
  unfold normalMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-! ## 向量运算工具（matvecE 与 mulVec 的定义等价） -/

/-- 向量减法的 matvecE 桥：matvecE A (x − y) = matvecE A x − matvecE A y。
（命名后缀 `_vec`：为避免与 `RealSparsity.matvecE_sub` 跨文件重名而改名；注意两者语义不同——
`RealSparsity.matvecE_sub` 是「矩阵差 (A−B) 作用于 x」，本引理是「A 作用于向量差 x−y」。） -/
lemma matvecE_sub_vec (A : Matrix (Fin m) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    matvecE A (x - y) = matvecE A x - matvecE A y := by
  change Matrix.mulVec A (x - y) = Matrix.mulVec A x - Matrix.mulVec A y
  rw [Matrix.mulVec_sub]

lemma matvecE_one (x : EuclideanSpace ℝ (Fin n)) :
    matvecE (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  change Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℝ) x = x
  rw [Matrix.one_mulVec]

lemma matvecE_zero (A : Matrix (Fin m) (Fin n) ℝ) :
    matvecE A (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  change Matrix.mulVec A (0 : EuclideanSpace ℝ (Fin n)) = 0
  rw [Matrix.mulVec_zero]

/-! ## 定理一、二：Penrose 等式 1 与 2 -/

/-- Penrose 等式 1：A A⁺ A = A。 -/
theorem pseudoInverse_penrose_eq1 (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) :
    A * pseudoInverse A * A = A := by
  calc
    A * pseudoInverse A * A = A * (normalMatrix A)⁻¹ * (normalMatrix A) := by
      simp only [pseudoInverse, normalMatrix, Matrix.mul_assoc]
    _ = A := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul (normalMatrix A) h, Matrix.mul_one]

/-- Penrose 等式 2：A⁺ A A⁺ = A⁺。 -/
theorem pseudoInverse_penrose_eq2 (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) :
    pseudoInverse A * A * pseudoInverse A = pseudoInverse A := by
  calc
    pseudoInverse A * A * pseudoInverse A =
        (normalMatrix A)⁻¹ * (normalMatrix A) * pseudoInverse A := by
      simp only [pseudoInverse, normalMatrix, Matrix.mul_assoc]
    _ = pseudoInverse A := by
      rw [Matrix.nonsing_inv_mul (normalMatrix A) h, Matrix.one_mul]

/-- A⁺ A = 1（满列秩时 A⁺ 是左逆）。 -/
theorem pseudoInverse_mul_self (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) :
    pseudoInverse A * A = 1 := by
  calc
    pseudoInverse A * A = (normalMatrix A)⁻¹ * (normalMatrix A) := by
      simp only [pseudoInverse, normalMatrix, Matrix.mul_assoc]
    _ = 1 := Matrix.nonsing_inv_mul (normalMatrix A) h

/-! ## 定理三、四：Penrose 等式 3 与 4 -/

/-- Penrose 等式 3：(A A⁺)ᵀ = A A⁺（自伴；实际上不需要 AᵀA 可逆）。 -/
theorem pseudoInverse_penrose_eq3 (A : Matrix (Fin m) (Fin n) ℝ) :
    (A * pseudoInverse A)ᵀ = A * pseudoInverse A := by
  have hGt := normalMatrix_transpose A
  calc
    (A * pseudoInverse A)ᵀ = (A * Matrix.transpose ((normalMatrix A)⁻¹)) * Aᵀ := by
      simp only [pseudoInverse, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = A * (normalMatrix A)⁻¹ * Aᵀ := by rw [Matrix.transpose_nonsing_inv, hGt]
    _ = A * pseudoInverse A := by simp only [pseudoInverse, Matrix.mul_assoc]

/-- Penrose 等式 4：(A⁺ A)ᵀ = A⁺ A。 -/
theorem pseudoInverse_penrose_eq4 (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) :
    (pseudoInverse A * A)ᵀ = pseudoInverse A * A := by
  rw [pseudoInverse_mul_self A h, Matrix.transpose_one]

/-! ## 定理五：法方程 -/

/-- (AᵀA)·A⁺ = Aᵀ。 -/
theorem normalMatrix_mul_pseudoInverse (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) :
    normalMatrix A * pseudoInverse A = Aᵀ := by
  calc
    normalMatrix A * pseudoInverse A = (normalMatrix A) * (normalMatrix A)⁻¹ * Aᵀ := by
      simp only [pseudoInverse, Matrix.mul_assoc]
    _ = Aᵀ := by
      rw [Matrix.mul_nonsing_inv (normalMatrix A) h, Matrix.one_mul]

/-- 定理五：x = A⁺b 满足法方程 AᵀA x = Aᵀb。 -/
theorem normal_equation_of_pseudoInverse (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) (b : EuclideanSpace ℝ (Fin m)) :
    matvecE (normalMatrix A) (matvecE (pseudoInverse A) b) = matvecE Aᵀ b := by
  rw [← matvecE_mul, normalMatrix_mul_pseudoInverse A h]

/-! ## 定理六：法方程解的唯一性 -/

/-- 定理六：AᵀA 可逆时法方程 AᵀA x = Aᵀb 的解唯一。 -/
theorem normal_equation_unique (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) (b : EuclideanSpace ℝ (Fin m))
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : matvecE (normalMatrix A) x = matvecE Aᵀ b)
    (hy : matvecE (normalMatrix A) y = matvecE Aᵀ b) : x = y := by
  have hsub : matvecE (normalMatrix A) (x - y) = 0 := by
    rw [matvecE_sub_vec, hx, hy, sub_self]
  have hz : matvecE (normalMatrix A)⁻¹ (matvecE (normalMatrix A) (x - y)) =
      matvecE (normalMatrix A)⁻¹ (0 : EuclideanSpace ℝ (Fin n)) := by
    rw [hsub]
  have hcomb : matvecE ((normalMatrix A)⁻¹ * normalMatrix A) (x - y) = 0 := by
    rw [matvecE_mul]
    rw [hsub]
    exact matvecE_zero _
  rw [Matrix.nonsing_inv_mul (normalMatrix A) h, matvecE_one] at hcomb
  exact sub_eq_zero.mp hcomb

/-! ## 定理七：最小二乘全局最优性 -/

/-- 定理七：x = A⁺b 是全局最小二乘解：
∀y，‖A(A⁺b) − b‖² ≤ ‖A y − b‖²。 -/
theorem pseudoInverse_leastSquares_optimal (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) (b : EuclideanSpace ℝ (Fin m)) :
    ∀ y : EuclideanSpace ℝ (Fin n),
      ‖matvecE A (matvecE (pseudoInverse A) b) - b‖ ^ 2 ≤ ‖matvecE A y - b‖ ^ 2 := by
  intro y
  -- 残差正交：⟪A(y − A⁺b), A(A⁺b) − b⟫ = 0
  have horth : (inner (matvecE A (y - matvecE (pseudoInverse A) b))
      (matvecE A (matvecE (pseudoInverse A) b) - b) : ℝ) = 0 := by
    rw [matvecE_adjoint_eq]
    have hNE : matvecE Aᵀ (matvecE A (matvecE (pseudoInverse A) b) - b) = 0 := by
      rw [matvecE_sub_vec, ← matvecE_mul]
      change matvecE (normalMatrix A) (matvecE (pseudoInverse A) b) - matvecE Aᵀ b = 0
      rw [normal_equation_of_pseudoInverse A h b, sub_self]
    rw [hNE, inner_zero_right]
  -- 分解：A y − b = A(y − A⁺b) + (A(A⁺b) − b)
  have hdecomp : matvecE A y - b =
      matvecE A (y - matvecE (pseudoInverse A) b) +
        (matvecE A (matvecE (pseudoInverse A) b) - b) := by
    rw [matvecE_sub_vec]
    abel
  rw [hdecomp, norm_add_sq_real, horth]
  simp only [mul_zero, add_zero]
  nlinarith [sq_nonneg (‖matvecE A (y - matvecE (pseudoInverse A) b)‖)]

/-! ## 定理八：A A⁺ 是到 range A 的正交投影 -/

/-- A A⁺ 幂等：(A A⁺)(A A⁺) = A A⁺。 -/
theorem projection_idempotent (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) :
    (A * pseudoInverse A) * (A * pseudoInverse A) = A * pseudoInverse A := by
  calc
    (A * pseudoInverse A) * (A * pseudoInverse A) = A * (pseudoInverse A * (A * pseudoInverse A)) := by
      rw [Matrix.mul_assoc]
    _ = A * ((pseudoInverse A * A) * pseudoInverse A) := by rw [Matrix.mul_assoc]
    _ = A * pseudoInverse A := by rw [pseudoInverse_mul_self A h, Matrix.one_mul]

/-- A A⁺ 固定 range A 中的向量：A A⁺ (A v) = A v。 -/
theorem projection_fixes_range (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) (v : EuclideanSpace ℝ (Fin n)) :
    matvecE (A * pseudoInverse A) (matvecE A v) = matvecE A v := by
  rw [← matvecE_mul, pseudoInverse_penrose_eq1 A h]

/-- A A⁺ 的值域含于 range A（像通过 A 分解）。 -/
theorem projection_range_subset (A : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m)) :
    matvecE (A * pseudoInverse A) y = matvecE A (matvecE (pseudoInverse A) y) :=
  matvecE_mul A (pseudoInverse A) y

/-- 定理八：A A⁺ 是到 range A 的正交投影（幂等 + 自伴 + 固定 range A + range ⊆ range A）。 -/
theorem projection_onto_range (A : Matrix (Fin m) (Fin n) ℝ)
    (h : IsUnit (normalMatrix A).det) :
    ((A * pseudoInverse A) * (A * pseudoInverse A) = A * pseudoInverse A) ∧
    ((A * pseudoInverse A)ᵀ = A * pseudoInverse A) ∧
    (∀ v : EuclideanSpace ℝ (Fin n), matvecE (A * pseudoInverse A) (matvecE A v) = matvecE A v) ∧
    (∀ y : EuclideanSpace ℝ (Fin m),
      matvecE (A * pseudoInverse A) y = matvecE A (matvecE (pseudoInverse A) y)) :=
  ⟨projection_idempotent A h, pseudoInverse_penrose_eq3 A,
    projection_fixes_range A h, projection_range_subset A⟩

/-! ## 注：与最小二乘/编辑线的关系
  · x = A⁺b 是法方程的唯一解（定理五 + 六），且是全局最小二乘解（定理七）；
  · A A⁺ 是 range A 上的正交投影（定理八），对应「LeastSquares 的正交投影」；
  · 诚实标注：完整 Moore–Penrose 定理（任意矩阵、唯一性、四条件等价）
    需要 SVD，mathlib 4.14 缺失，故本文件只覆盖满列秩构造。 -/

end Lattice
