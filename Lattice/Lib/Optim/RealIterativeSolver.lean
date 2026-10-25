import Mathlib
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: 迭代线性求解器收敛 —— Richardson 收缩 / Jacobi 对角预处理 / 预条件形式

迭代法求解 A x = b 的**收缩-收敛**理论（对接 RealConvergence 的 ε-终止骨架）：

  1. `richardson`：x' = x − ω(A x − b)（基本迭代格式）；
  2. `richardson_error`：精确解 xs 下 x' − xs = (1 − ωA)(x − xs)
     （误差的线性算子形式，迭代的核心恒等式）；
  3. `richardson_contraction`：‖1 − ωA‖ ≤ c ⟹ 误差每步收缩 c 倍；
  4. `richardsonIterate` / `richardsonIterate_succ`：迭代序列（`Function.iterate`）；
  5. `richardson_converges`：0 ≤ c < 1 时 ∀ε>0，∃k，误差 < ε
     （直接调用 `RealConvergence.contraction_converges`）；
  6. `richardson_converges_geometric`：几何界 ‖eₖ‖ ≤ c^k·‖e₀‖；
  7. `jacobiStep` / `jacobiIterMatrix`（矩阵级）：对角预处理迭代
     x' = x − D⁻¹(A x − b)，迭代矩阵 1 − D⁻¹A；
  8. `jacobi_contraction`：‖1 − D⁻¹A‖ ≤ c ⟹ Jacobi 误差每步收缩 c；
  9. `diag_dominant_iter_matrix_row_sum_lt_one`：严格对角占优 ⟹
     迭代矩阵的**行和**（∞-范数）< 1 —— 纯逐元素 Finset 计算；
 10. `preconditionedRichardson_contraction`（Gauss–Seidel 的一般形式）：
     以 M⁻¹ 为左预条件的迭代在 ‖1 − ωM⁻¹A‖ ≤ c 时收缩。

诚实假设与降级（明确标注）：
  · 收敛性依赖**先验收缩假设** ‖1 − ωA‖ ≤ c < 1（对 Richardson 即
    «谱半径 < 1» 的充分条件）；由 A 的具体结构（如对称正定 + 0<ω<2/λmax）
    推出该假设的谱分析未形式化（需要特征分解 API）；
  · Jacobi 的 `jacobi_contraction` 同样以下述假设为条件：迭代矩阵的
    **欧氏算子范数** ≤ c < 1；严格对角占优给出的行和界
    （`diag_dominant_iter_matrix_row_sum_lt_one`，∞-范数）到欧氏
    算子范数 ‖M‖₂ ≤ √(‖M‖₁‖M‖_∞) 的抬升**未形式化**（诚实降级）；
  · 对角非零假设：`hdiag : ∀ i, A i i ≠ 0`（否则 D⁻¹ 不存在）；
  · Gauss–Seidel 严格三角形式的收缩界未形式化，本文件给出其
    「左预条件 Richardson」的一般形式与其收缩定理。

模型无关：任意 ℝ-赋范空间（Richardson 部分）；Fin 方阵（Jacobi 部分）。
无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

open Matrix
open scoped BigOperators

/-! ## Richardson 迭代（抽象赋范空间） -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Richardson 迭代：x' = x − ω(A x − b)。 -/
def richardson (A : E →L[ℝ] E) (b : E) (ω : ℝ) (x : E) : E := x - ω • (A x - b)

/-- 误差恒等式：A xs = b ⟹ richerdson(A,b,ω,x) − xs = (1 − ωA)(x − xs)。 -/
theorem richardson_error (A : E →L[ℝ] E) (b xs x : E) (ω : ℝ) (hxs : A xs = b) :
    richardson A b ω x - xs = (ContinuousLinearMap.id ℝ E - ω • A) (x - xs) := by
  have h1 : richardson A b ω x - xs = x - xs - ω • (A x - b) := by
    unfold richardson
    abel
  have h2 : (ContinuousLinearMap.id ℝ E - ω • A) (x - xs) = x - xs - ω • (A x - b) := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
      map_sub, hxs]
  rw [h1, h2]

/-- 收缩定理：‖1 − ωA‖ ≤ c ⟹ ‖richardson − xs‖ ≤ c·‖x − xs‖。 -/
theorem richardson_contraction (A : E →L[ℝ] E) (b xs x : E) (ω c : ℝ)
    (hxs : A xs = b) (hc : ‖ContinuousLinearMap.id ℝ E - ω • A‖ ≤ c) :
    ‖richardson A b ω x - xs‖ ≤ c * ‖x - xs‖ := by
  rw [richardson_error A b xs x ω hxs]
  calc
    ‖(ContinuousLinearMap.id ℝ E - ω • A) (x - xs)‖ ≤
        ‖ContinuousLinearMap.id ℝ E - ω • A‖ * ‖x - xs‖ :=
      (ContinuousLinearMap.id ℝ E - ω • A).le_opNorm _
    _ ≤ c * ‖x - xs‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-- Richardson 迭代序列 xₖ = (x ↦ x − ω(Ax − b))^[k] x₀。 -/
def richardsonIterate (A : E →L[ℝ] E) (b : E) (ω : ℝ) (x0 : E) : ℕ → E :=
  fun k => (fun x => richardson A b ω x)^[k] x0

lemma richardsonIterate_succ (A : E →L[ℝ] E) (b : E) (ω : ℝ) (x0 : E) (k : ℕ) :
    richardsonIterate A b ω x0 (k + 1) = richardson A b ω (richardsonIterate A b ω x0 k) := by
  unfold richardsonIterate
  rw [Function.iterate_succ_apply']

/-- 误差递推：e_{k+1} 的误差算子作用形式。 -/
lemma richardsonIterate_error (A : E →L[ℝ] E) (b xs : E) (ω : ℝ) (x0 : E)
    (hxs : A xs = b) (k : ℕ) :
    richardsonIterate A b ω x0 (k + 1) - xs =
      (ContinuousLinearMap.id ℝ E - ω • A) (richardsonIterate A b ω x0 k - xs) := by
  rw [richardsonIterate_succ]
  exact richardson_error A b xs (richardsonIterate A b ω x0 k) ω hxs

/-- 主定理：0 ≤ c < 1 且 ‖1 − ωA‖ ≤ c ⟹ Richardson 迭代 ε-终止。 -/
theorem richardson_converges (A : E →L[ℝ] E) (b xs x0 : E) (ω c : ℝ)
    (hxs : A xs = b) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ‖ContinuousLinearMap.id ℝ E - ω • A‖ ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ‖richardsonIterate A b ω x0 k - xs‖ < ε := by
  have hstep : ∀ k : ℕ,
      ‖richardsonIterate A b ω x0 (k + 1) - xs‖ ≤ c * ‖richardsonIterate A b ω x0 k - xs‖ := by
    intro k
    rw [richardsonIterate_succ]
    exact richardson_contraction A b xs (richardsonIterate A b ω x0 k) ω c hxs hc
  have := contraction_converges
    (e := fun k => ‖richardsonIterate A b ω x0 k - xs‖) c
    hc0 hc1 hstep (fun k => norm_nonneg _)
  exact this

/-- 几何衰减界：‖eₖ‖ ≤ c^k·‖e₀‖。 -/
theorem richardson_converges_geometric (A : E →L[ℝ] E) (b xs x0 : E) (ω c : ℝ)
    (hxs : A xs = b) (hc0 : 0 ≤ c)
    (hc : ‖ContinuousLinearMap.id ℝ E - ω • A‖ ≤ c) :
    ∀ k : ℕ, ‖richardsonIterate A b ω x0 k - xs‖ ≤ c ^ k * ‖richardsonIterate A b ω x0 0 - xs‖ := by
  have hstep : ∀ k : ℕ,
      ‖richardsonIterate A b ω x0 (k + 1) - xs‖ ≤ c * ‖richardsonIterate A b ω x0 k - xs‖ := by
    intro k
    rw [richardsonIterate_succ]
    exact richardson_contraction A b xs (richardsonIterate A b ω x0 k) ω c hxs hc
  exact contraction_pow_bound (e := fun k => ‖richardsonIterate A b ω x0 k - xs‖) c hc0 hstep

/-! ## 矩阵桥（matCLME 的减法与单位） -/

variable {m n : ℕ}

/-- 矩阵减法的 matCLME 桥：matCLME (M − N) = matCLME M − matCLME N。
（命名前缀 `richardson_`：为避免与既有 `RealSparsity.matCLME_sub` 跨文件重名而前缀化。） -/
lemma richardson_matCLME_sub (M N : Matrix (Fin m) (Fin n) ℝ) :
    matCLME (M - N) = matCLME M - matCLME N := by
  apply ContinuousLinearMap.ext
  intro x
  rw [matCLME_apply, ContinuousLinearMap.sub_apply, matCLME_apply, matCLME_apply]
  change Matrix.mulVec (M - N) x = Matrix.mulVec M x - Matrix.mulVec N x
  rw [Matrix.sub_mulVec]

lemma matCLME_one :
    matCLME (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [matCLME_apply, ContinuousLinearMap.id_apply]
  change Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℝ) x = x
  rw [Matrix.one_mulVec]

/-! ## Jacobi 对角预处理迭代（矩阵级） -/

/-- 对角缩放矩阵 D⁻¹ = diag(dᵢ⁻¹)。 -/
def diagScale (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (d i)⁻¹)

/-- Jacobi 迭代矩阵：1 − D⁻¹A。 -/
def jacobiIterMatrix (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := 1 - diagScale d * A

/-- Jacobi 迭代：x' = x − D⁻¹(A x − b)（取 ω = 1 的 Richardson，作用在 D⁻¹A 上）。 -/
def jacobiStep (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (b x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  richardson (matCLME (diagScale d * A)) (matvecE (diagScale d) b) 1 x

/-- 迭代算子恒等式：1 − 1·(D⁻¹A) = 1 − D⁻¹A（作为连续线性算子）。 -/
lemma jacobi_operator_eq (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - (1 : ℝ) • matCLME (diagScale d * A) =
      matCLME (jacobiIterMatrix A d) := by
  rw [one_smul, jacobiIterMatrix, richardson_matCLME_sub, matCLME_one]

/-- Jacobi 收缩：迭代矩阵算子范数 ≤ c ⟹ 误差每步收缩 c。 -/
theorem jacobi_contraction (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (b xs x : EuclideanSpace ℝ (Fin n)) (hxs : matvecE A xs = b) (c : ℝ)
    (hc : ‖matCLME (jacobiIterMatrix A d)‖ ≤ c) :
    ‖jacobiStep A d b x - xs‖ ≤ c * ‖x - xs‖ := by
  have hxs' : matCLME (diagScale d * A) xs = matvecE (diagScale d) b := by
    rw [matCLME_apply, matvecE_mul, hxs]
  have hc' : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
      (1 : ℝ) • matCLME (diagScale d * A)‖ ≤ c := by
    rwa [jacobi_operator_eq A d]
  exact richardson_contraction (matCLME (diagScale d * A)) (matvecE (diagScale d) b) xs x 1 c hxs' hc'

/-- 严格对角占优 ⟹ Jacobi 迭代矩阵的行和（∞-范数）< 1。
逐元素展开：对角元 = 0，非对角元 = −(Aᵢᵢ)⁻¹Aᵢⱼ，行和 = |Aᵢᵢ|⁻¹·Σ_{j≠i}|Aᵢⱼ|。 -/
theorem diag_dominant_iter_matrix_row_sum_lt_one (A : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, A i i ≠ 0)
    (hdom : ∀ i, ∑ j in (Finset.univ.erase i), |A i j| < |A i i|) :
    ∀ i, ∑ j : Fin n, |jacobiIterMatrix A (fun i => A i i) i j| < 1 := by
  intro i
  have hpos : 0 < |A i i| := abs_pos.mpr (hdiag i)
  have hdiag0 : jacobiIterMatrix A (fun i => A i i) i i = 0 := by
    unfold jacobiIterMatrix diagScale
    rw [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul, if_pos rfl,
      inv_mul_cancel₀ (hdiag i), sub_self]
  have hoff : ∀ j : Fin n, j ≠ i →
      |jacobiIterMatrix A (fun i => A i i) i j| = |A i i|⁻¹ * |A i j| := by
    intro j hji
    unfold jacobiIterMatrix diagScale
    rw [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
      if_neg (fun h : i = j => hji h.symm), zero_sub, abs_neg, abs_mul, abs_inv]
  have hsum_erase : (∑ j in (Finset.univ.erase i),
        |jacobiIterMatrix A (fun i => A i i) i j|) =
      |A i i|⁻¹ * ∑ j in (Finset.univ.erase i), |A i j| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hoff j (Finset.mem_erase.mp hj).1]
  have hsplit := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)
    (fun j => |jacobiIterMatrix A (fun i => A i i) i j|)
  rw [Finset.sdiff_singleton_eq_erase] at hsplit
  rw [hsplit, hdiag0, abs_zero, add_zero, hsum_erase]
  calc
    |A i i|⁻¹ * (∑ j in (Finset.univ.erase i), |A i j|) < |A i i|⁻¹ * |A i i| :=
      mul_lt_mul_of_pos_left (hdom i) (inv_pos.mpr hpos)
    _ = 1 := inv_mul_cancel₀ (abs_ne_zero.mpr (hdiag i))

/-! ## 预条件 Richardson（Gauss–Seidel 的一般形式） -/

/-- 左预条件 Richardson：x' = x − ω·M⁻¹(A x − b)（Gauss–Seidel 取 M = D + L）。 -/
def preconditionedRichardson (Minv A : Matrix (Fin n) (Fin n) ℝ)
    (b x : EuclideanSpace ℝ (Fin n)) (ω : ℝ) : EuclideanSpace ℝ (Fin n) :=
  richardson (matCLME (Minv * A)) (matvecE Minv b) ω x

/-- 预条件收缩：‖1 − ωM⁻¹A‖ ≤ c ⟹ 误差每步收缩 c（Gauss–Seidel 的界的一般形式）。 -/
theorem preconditionedRichardson_contraction (Minv A : Matrix (Fin n) (Fin n) ℝ)
    (b xs x : EuclideanSpace ℝ (Fin n)) (ω c : ℝ) (hxs : matvecE A xs = b)
    (hc : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
      ω • matCLME (Minv * A)‖ ≤ c) :
    ‖preconditionedRichardson Minv A b x ω - xs‖ ≤ c * ‖x - xs‖ := by
  have hxs' : matCLME (Minv * A) xs = matvecE Minv b := by
    rw [matCLME_apply, matvecE_mul, hxs]
  exact richardson_contraction (matCLME (Minv * A)) (matvecE Minv b) xs x ω c hxs' hc

/-! ## 注：诚实降级汇总
  · 所有收敛结论都建立在**先验收缩假设** ‖1 − ωA‖ ≤ c < 1 上；
    「由 A 的谱条件推出该假设」需要特征值/谱半径理论（见 RealSpectral
    只能给出实特征值界，故未接入）；
  · Jacobi：`diag_dominant_iter_matrix_row_sum_lt_one` 给出严格对角占优
    ⟹ 迭代矩阵行和 < 1（∞-范数意义）；**未**把它抬升为欧氏算子范数界，
    因此 `jacobi_contraction` 以算子范数假设为条件（明确降级）；
  · Gauss–Seidel：只给出左预条件 Richardson 的一般收缩定理，严格
    「M = D + L」的三角结构与收缩常数的推导未形式化。 -/

end Lattice
