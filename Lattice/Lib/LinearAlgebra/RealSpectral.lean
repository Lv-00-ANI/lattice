import Mathlib
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: 实谱界 —— Gershgorin 圆盘 / 谱半径 ≤ 算子范数 / 幂迭代增长率

初等实谱理论（**只处理实特征对**：特征向量 x ∈ ℝⁿ，特征值 μ ∈ ℝ）：

  1. `HasRealEigenpair` / `HasRealEigenvalue`：实特征对与实特征值的定义
     （mathlib 4.14 无 `Matrix.HasEigenvector`，自定义）；
  2. `gershgorin_bound`：Gershgorin 圆盘包含实谱——
     若 A x = μ x（x ≠ 0），则 ∃ i，|μ − Aᵢᵢ| ≤ Σ_{j≠i} |Aᵢⱼ|
     （取最大分量坐标 i，逐坐标展开 + 三角不等式 + 消去 |xᵢ| > 0）；
  3. `spectral_radius_le_opNorm`：谱半径 ≤ 算子范数：|μ| ≤ ‖matCLME A‖；
  4. `eigenvalue_abs_le_frobenius`：|μ| ≤ ‖A‖_F（上述 + opNorm_le_frobenius）；
  5. `eigenvalue_abs_le_row_sum`：Gershgorin 的直接推论
     |μ| ≤ |Aᵢᵢ| + Σ_{j≠i}|Aᵢⱼ|（即圆盘中心 + 半径）；
  6. `power_iteration_bound`：幂迭代增长率界
     ∀k，‖A^k x‖ ≤ ‖A‖^k·‖x‖（归纳 + `le_opNorm`）；
  7. `power_iteration_ratio_bound`：相邻迭代比 ≤ ‖A‖（幂迭代的收缩率上界）。

诚实标注与降级：
  · 只覆盖**实**特征值；复谱（一般实矩阵可有非实特征值）需要 ℂ 上的谱理论，
    本文件不声称；
  · 因此「谱半径 = max|μ|」在复谱情形下未被形式化；这里给出的是
    「每个实特征值都满足的界」；
  · 未形式化 Perron–Frobenius、Perron 根、对称矩阵谱定理（需要特征分解 API）；
  · `eigenvalue_abs_le_row_sum` 用 `∑_{j≠i}` 形式而非 `max`（避免 `sup` 的非空性负担）。

模型无关：任意 Fin 维度实方阵。无 sorry/axiom/admit。
-/

noncomputable section

open scoped InnerProduct

namespace Lattice

open Matrix
open scoped BigOperators

variable {m n : ℕ}

/-! ## 实特征对 / 实特征值 -/

/-- 实特征对：非零向量 x 满足 A x = μ x。 -/
def HasRealEigenpair (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ≠ 0 ∧ matvecE A x = μ • x

/-- 实特征值：存在实特征向量。 -/
def HasRealEigenvalue (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : Prop :=
  ∃ x : EuclideanSpace ℝ (Fin n), HasRealEigenpair A μ x

/-! ## 分量工具 -/

lemma eq_zero_of_all_coord_zero {x : EuclideanSpace ℝ (Fin n)} (h : ∀ i, x i = 0) : x = 0 := by
  ext i
  simpa using h i

lemma exists_coord_ne_zero {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) : ∃ i, x i ≠ 0 := by
  by_contra h
  rw [not_exists] at h
  simp only [not_not] at h
  exact hx (eq_zero_of_all_coord_zero h)

lemma exists_max_coord (x : EuclideanSpace ℝ (Fin n)) [Nonempty (Fin n)] :
    ∃ i : Fin n, ∀ j : Fin n, |x j| ≤ |x i| := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun j => |x j|) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-! ## 定理一：Gershgorin 圆盘 -/

/-- 定理一（Gershgorin）：实特征值落在某个 Gershgorin 圆盘内：
∃ i，|μ − Aᵢᵢ| ≤ Σ_{j≠i}|Aᵢⱼ|。 -/
theorem gershgorin_bound (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (h : HasRealEigenpair A μ x) :
    ∃ i : Fin n, |μ - A i i| ≤ ∑ j in (Finset.univ.erase i), |A i j| := by
  obtain ⟨hxne, hxeq⟩ := h
  obtain ⟨i₀, hi₀⟩ := exists_coord_ne_zero hxne
  haveI : Nonempty (Fin n) := ⟨i₀⟩
  obtain ⟨i, hmax⟩ := exists_max_coord x
  refine ⟨i, ?_⟩
  -- 第 i 个坐标的等式：Σ_j Aᵢⱼ xⱼ = μ xᵢ
  have hcoord : (∑ j : Fin n, A i j * x j) = μ * x i := by
    have h1 : matvecE A x i = (μ • x) i := by rw [hxeq]
    simpa [matvecE] using h1
  -- xᵢ ≠ 0（否则由最大性所有分量为零）
  have hxi : x i ≠ 0 := by
    intro h0
    have hall : ∀ j : Fin n, x j = 0 := by
      intro j
      have hj : |x j| ≤ 0 := by
        have := hmax j
        rw [h0, abs_zero] at this
        exact this
      exact abs_eq_zero.mp (le_antisymm hj (abs_nonneg _))
    exact hi₀ (hall i₀)
  -- 消去对角项：(μ − Aᵢᵢ)·xᵢ = Σ_{j≠i} Aᵢⱼ xⱼ
  have hsplit : (∑ j in (Finset.univ.erase i), A i j * x j) = (μ - A i i) * x i := by
    have h1 := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) (fun j => A i j * x j)
    rw [hcoord] at h1
    have h2 : (∑ j in (Finset.univ.erase i), A i j * x j) =
        ∑ j in (Finset.univ \ {i}), A i j * x j := by
      simp [Finset.sdiff_singleton_eq_erase]
    rw [h2]
    linarith
  -- 取绝对值并逐项用最大性放大
  have habs : |μ - A i i| * |x i| ≤
      (∑ j in (Finset.univ.erase i), |A i j|) * |x i| := by
    calc
      |μ - A i i| * |x i| = |(μ - A i i) * x i| := (abs_mul _ _).symm
      _ = |∑ j in (Finset.univ.erase i), A i j * x j| := by rw [hsplit]
      _ ≤ ∑ j in (Finset.univ.erase i), |A i j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j in (Finset.univ.erase i), |A i j| * |x j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul]
      _ ≤ ∑ j in (Finset.univ.erase i), |A i j| * |x i| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg _)
      _ = (∑ j in (Finset.univ.erase i), |A i j|) * |x i| := by rw [Finset.sum_mul]
  exact le_of_mul_le_mul_right habs (abs_pos.mpr hxi)

/-! ## 定理二：谱半径 ≤ 算子范数 -/

/-- 定理二：|μ| ≤ ‖matCLME A‖（实特征值被算子范数控制）。 -/
theorem spectral_radius_le_opNorm (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (h : HasRealEigenvalue A μ) : |μ| ≤ ‖matCLME A‖ := by
  obtain ⟨x, hxne, hxeq⟩ := h
  have h1 : ‖matCLME A x‖ ≤ ‖matCLME A‖ * ‖x‖ := (matCLME A).le_opNorm x
  rw [matCLME_apply, hxeq, norm_smul, Real.norm_eq_abs] at h1
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hxne)

/-- 定理三：|μ| ≤ ‖A‖_F（Frobenius 界）。 -/
theorem eigenvalue_abs_le_frobenius (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (h : HasRealEigenvalue A μ) : |μ| ≤ frobeniusNorm A :=
  le_trans (spectral_radius_le_opNorm A μ h) (opNorm_le_frobenius A)

/-- 定理四：Gershgorin 推论 |μ| ≤ |Aᵢᵢ| + Σ_{j≠i}|Aᵢⱼ|。 -/
theorem eigenvalue_abs_le_row_sum (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (h : HasRealEigenpair A μ x) :
    ∃ i : Fin n, |μ| ≤ |A i i| + ∑ j in (Finset.univ.erase i), |A i j| := by
  obtain ⟨i, hi⟩ := gershgorin_bound A μ x h
  refine ⟨i, ?_⟩
  calc
    |μ| = |(μ - A i i) + A i i| := by congr 1; ring
    _ ≤ |μ - A i i| + |A i i| := abs_add _ _
    _ ≤ |A i i| + ∑ j in (Finset.univ.erase i), |A i j| := by linarith

/-! ## 定理五、六：幂迭代增长率界 -/

/-- 定理五：‖(A^k) x‖ ≤ ‖A‖^k·‖x‖（迭代算子的幂增长率上界）。 -/
theorem power_iteration_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∀ k : ℕ, ‖(matCLME A)^[k] x‖ ≤ ‖matCLME A‖ ^ k * ‖x‖ := by
  intro k
  induction k with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖matCLME A ((matCLME A)^[k] x)‖ ≤ ‖matCLME A‖ * ‖(matCLME A)^[k] x‖ :=
          (matCLME A).le_opNorm _
        _ ≤ ‖matCLME A‖ * (‖matCLME A‖ ^ k * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg _)
        _ = ‖matCLME A‖ ^ (k + 1) * ‖x‖ := by ring

/-- 定理六：幂迭代相邻比 ‖A^{k+1}x‖/‖A^k x‖ ≤ ‖A‖（非零分母）。 -/
theorem power_iteration_ratio_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) (h : (matCLME A)^[k] x ≠ 0) :
    ‖(matCLME A)^[k + 1] x‖ / ‖(matCLME A)^[k] x‖ ≤ ‖matCLME A‖ := by
  rw [Function.iterate_succ_apply', div_le_iff₀ (norm_pos_iff.mpr h)]
  exact (matCLME A).le_opNorm _

/-! ## 注：诚实降级
  · 本文件只处理实特征对；一般实矩阵的非实特征值（复共轭对）不在范围内，
    需要 ℂ 上的谱理论（mathlib 4.14 的 `Module.End.HasEigenvalue` 可用于
    复化，但实矩阵的复特征值需先把矩阵嵌入 ℂ）；
  · Gershgorin 定理（定理一）对**任意**实特征对成立，不要求对称性；
  · 「谱半径」在此仅指 max over 实特征值，非复谱半径。 -/

end Lattice
