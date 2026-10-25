import Mathlib
import Lattice.Lib.LinearAlgebra.RealSpectral
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: 谱半径（对角 / 一维情形）与对角算子范数恒等式

本文件在 `RealSpectral`（实谱界：Gershgorin 与 |μ| ≤ ‖A‖）与 `RealMatrixNorm`
（Fin 矩阵的算子范数）之上，把**对角矩阵的谱半径**这一可完整处理的情形做出来：

  1. `diagRadius`：对角谱半径 `ρ̂(d) = max_i |dᵢ|`（`Finset.sup'`，需 `Nonempty (Fin n)`）；
     基本性质：`abs_le_diagRadius`、`diagRadius_nonneg`、`diagRadius_pow`
     （`ρ̂(d^k) = ρ̂(d)^k`，对一切 `k` 成立）；
  2. 特征结构：`diagonal_eigenpair`（`diag d` 作用在 `eᵢ` 上是数乘 `dᵢ`）与
     `diagonal_hasRealEigenvalue`（`dᵢ` 是实特征值）；
  3. 谱半径上界：`diag_eigenvalue_abs_le`——由 `RealSpectral.gershgorin_bound` 得
     非对角 Gershgorin 和为 0，故实特征值必为某 `dᵢ`，于是 `|μ| ≤ ρ̂(d)`；
     `spectral_radius_le_opNorm_diag` 只是 `RealSpectral.spectral_radius_le_opNorm`
     在对角情形下的实例化；
  4. **对角算子范数恒等式**（技术核心）：`opNorm_diagonal_le`（上下界之一半）、
     `le_opNorm_diagonal`（用单位基向量 `e_{i₀}` 取到最大模）与合成的
     `opNorm_diagonal : ‖matCLME (diag d)‖ = ρ̂(d)`；
  5. **对角的 Gelfand 公式**：`opNorm_diagonal_pow`（`‖(diag d)^k‖ = ρ̂(d)^k`）与
     `gelfand_diagonal`（`‖(diag d)^k‖^{1/k} → ρ̂(d)`，常数序列极限）；
  6. 一维特例：`diagRadius_one`（`Fin 1` 时 `ρ̂(d) = |d₀|`）与收敛条件
     `opNorm_diagonal_lt_one`（`ρ̂(d) < 1 → ‖matCLME (diag d)‖ < 1`）。

诚实标注与降级（无 sorry / axiom / admit）：
  · 本文件只完成**对角矩阵**上的谱半径刻画与 Gelfand 公式
    `ρ(T) = lim ‖Tⁿ‖^{1/n}`；
  · **一般算子的 Gelfand 公式：已由 `RealGelfand` 补出 `inf` 形式**——
    `RealGelfand.gelfand_radius_le_opNorm`（`ρ(T) ≤ ‖T‖`，**任意**实方阵，非对角）、
    `RealGelfand.gelfand_radius_eq_inf`（`ρ(T) = inf_{k>0} ‖Tᵏ‖^{1/k}`）
    与 `RealGelfand.gelfand_radius_pow_bounds`（`ρ(T)ᵏ ≤ ρ(Tᵏ) ≤ ‖T‖ᵏ`）。
    本文件原先标注的「一般算子 Gelfand 未做」**已部分闭合**：
    `inf` 形式与非对角 `ρ ≤ ‖T‖` 均已证；**等号 `ρ(Tᵏ) = ρ(T)ᵏ` 仍未证**
    （需 Gelfand 极限定理的**复语境适配**——注意该 `lim` 定理 **mathlib 4.14 已有**，
    `Spectrum.lean:374`，**不是**「mathlib 缺公式」，见 CORRECTIONS B25）；
  · **复谱未做**：只处理实特征值（`RealSpectral.HasRealEigenvalue`），
    一般实矩阵的非实特征值（复共轭对）**已由 `RealComplexSpectral` 补出**
    （`cspec_conj_isRoot_of_isRoot`：实矩阵特征多项式的根在共轭下封闭）；
  · `diagRadius` 需要 `Nonempty (Fin n)`（即 `n ≠ 0`）：空维数下 `sup'` 无定义，
    这是**诚实降级**为「非空对角阵」而非「任意维」；
  · 未做：非对角矩阵的谱半径（例如对称矩阵 `ρ = ‖A‖`，需要谱定理）、
    幂法收敛速度（`|λ₂/λ₁|^k`）；**标注**：`diagRadius_pow` 对一切 `k : ℕ` 成立
    （含 `k = 0`，此时两侧均为 `1`）。

模型无关：任意非空 `Fin n` 维对角实矩阵。
-/

noncomputable section

open scoped InnerProduct
open scoped Topology

namespace Lattice

open Matrix
open scoped BigOperators

variable {n : ℕ} [Nonempty (Fin n)]

/-! ## 一、对角谱半径 -/

/-- 对角谱半径 `ρ̂(d) = max_i |dᵢ|`（用 `Finset.sup'`；需要 `Fin n` 非空）。 -/
def diagRadius (d : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |d i|)

/-- 每个分量的模都被对角谱半径控制：`|dᵢ| ≤ ρ̂(d)`。 -/
theorem abs_le_diagRadius (d : Fin n → ℝ) (i : Fin n) : |d i| ≤ diagRadius d :=
  Finset.le_sup' (s := Finset.univ) (f := fun i => |d i|) (Finset.mem_univ i)

/-- 对角谱半径非负。 -/
theorem diagRadius_nonneg (d : Fin n → ℝ) : 0 ≤ diagRadius d := by
  obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
  exact le_trans (abs_nonneg (d i)) (abs_le_diagRadius d i)

/-- **对角谱半径的幂律**：`ρ̂(d^k) = ρ̂(d)^k`（对一切 `k : ℕ`，含 `k = 0`）。 -/
theorem diagRadius_pow (d : Fin n → ℝ) (k : ℕ) :
    diagRadius (fun i => d i ^ k) = (diagRadius d) ^ k := by
  apply le_antisymm
  · rw [diagRadius]
    refine (Finset.sup'_le_iff Finset.univ_nonempty (fun i : Fin n => |d i ^ k|)).mpr ?_
    intro i _
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg (d i)) (abs_le_diagRadius d i) k
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      (H := Finset.univ_nonempty) (f := fun i => |d i|)
    have hsup : diagRadius d = |d i₀| := hi₀
    rw [hsup, ← abs_pow]
    exact Finset.le_sup' (s := Finset.univ) (f := fun i => |d i ^ k|) (Finset.mem_univ i₀)

/-! ## 二、对角矩阵的特征结构 -/

/-- **对角特征方程**：`(diag d) eᵢ = dᵢ • eᵢ`（`eᵢ = EuclideanSpace.single i 1`）。 -/
theorem diagonal_eigenpair (d : Fin n → ℝ) (i : Fin n) :
    matvecE (Matrix.diagonal d) (EuclideanSpace.single i (1 : ℝ))
      = d i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  have h := congrFun (matvecE_single (Matrix.diagonal d) i) j
  simp only at h
  rw [h, Pi.smul_apply, smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    rw [Matrix.diagonal_apply_eq, EuclideanSpace.single_apply, if_pos rfl]
    ring
  · rw [Matrix.diagonal_apply_ne d hji, EuclideanSpace.single_apply, if_neg hji]
    ring

/-- `dᵢ` 是 `diag d` 的实特征值（特征向量 `eᵢ ≠ 0`）。 -/
theorem diagonal_hasRealEigenvalue (d : Fin n → ℝ) (i : Fin n) :
    HasRealEigenvalue (Matrix.diagonal d) (d i) := by
  refine ⟨EuclideanSpace.single i (1 : ℝ), ?_, diagonal_eigenpair d i⟩
  intro hzero
  have h1 := congrFun hzero i
  rw [EuclideanSpace.single_apply, if_pos rfl] at h1
  simp at h1

/-! ## 三、实特征值被对角谱半径控制 -/

/-- **对角实谱界**：`diag d` 的任意实特征值 `μ` 满足 `|μ| ≤ ρ̂(d)`。
证明：`gershgorin_bound` 给出某个圆盘，非对角项全为 0，故 `μ = dᵢ`，再用
`abs_le_diagRadius`。 -/
theorem diag_eigenvalue_abs_le (d : Fin n → ℝ) (mu : ℝ)
    (h : HasRealEigenvalue (Matrix.diagonal d) mu) : |mu| ≤ diagRadius d := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨i, hi⟩ := gershgorin_bound (Matrix.diagonal d) mu x hx
  have hzero : (∑ j in Finset.univ.erase i, |Matrix.diagonal d i j|) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [Matrix.diagonal_apply_ne d hji.symm, abs_zero]
  rw [hzero] at hi
  have hmu : mu = d i := by
    have hzero' : |mu - Matrix.diagonal d i i| = 0 := le_antisymm hi (abs_nonneg _)
    rw [abs_eq_zero, Matrix.diagonal_apply_eq] at hzero'
    linarith
  rw [hmu]
  exact abs_le_diagRadius d i

/-- 对角情形的「谱半径 ≤ 算子范数」：只是
`RealSpectral.spectral_radius_le_opNorm` 的实例化（不重复其证明）。 -/
theorem spectral_radius_le_opNorm_diag (d : Fin n → ℝ) (mu : ℝ)
    (h : HasRealEigenvalue (Matrix.diagonal d) mu) :
    |mu| ≤ ‖matCLME (Matrix.diagonal d)‖ :=
  spectral_radius_le_opNorm (Matrix.diagonal d) mu h

/-! ## 四、对角算子范数恒等式 -/

/-- 对角矩阵乘向量：`matvecE (diag d) x = fun i => dᵢ · xᵢ`。 -/
theorem matvecE_diagonal (d : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matvecE (Matrix.diagonal d) x = fun i => d i * x i := by
  ext i
  rw [matvecE, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne d hj.symm, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **对角算子范数上界**：`‖matCLME (diag d)‖ ≤ ρ̂(d)`。
逐点界 `‖(diag d) x‖ ≤ ρ̂(d) ‖x‖` 经 `opNorm_le_bound` 组装（两边平方，
用 `euclid_norm_sq_eq` 与 `|dᵢ| ≤ ρ̂(d)`）。 -/
theorem opNorm_diagonal_le (d : Fin n → ℝ) :
    ‖matCLME (Matrix.diagonal d)‖ ≤ diagRadius d := by
  refine ContinuousLinearMap.opNorm_le_bound _ (diagRadius_nonneg d) (fun x => ?_)
  rw [matCLME_apply]
  have hcoord : ∀ i : Fin n, matvecE (Matrix.diagonal d) x i = d i * x i := fun i =>
    (by simpa using congrFun (matvecE_diagonal d x) i)
  have hnat : ∀ i : Fin n, (d i) ^ 2 ≤ (diagRadius d) ^ 2 := fun i =>
    sq_le_sq.mpr (by simpa [abs_of_nonneg (diagRadius_nonneg d)] using abs_le_diagRadius d i)
  have hsq : ‖matvecE (Matrix.diagonal d) x‖ ^ 2 ≤ (diagRadius d * ‖x‖) ^ 2 := by
    calc ‖matvecE (Matrix.diagonal d) x‖ ^ 2
        = ∑ i : Fin n, (matvecE (Matrix.diagonal d) x i) ^ 2 := by rw [euclid_norm_sq_eq]
      _ = ∑ i : Fin n, (d i) ^ 2 * (x i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoord i, mul_pow]
      _ ≤ ∑ i : Fin n, (diagRadius d) ^ 2 * (x i) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (hnat i) (sq_nonneg _)
      _ = (diagRadius d) ^ 2 * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum, ← euclid_norm_sq_eq]
      _ = (diagRadius d * ‖x‖) ^ 2 := by ring
  have habs := sq_le_sq.mp hsq
  have ha : 0 ≤ ‖matvecE (Matrix.diagonal d) x‖ := norm_nonneg _
  have hb : 0 ≤ diagRadius d * ‖x‖ := mul_nonneg (diagRadius_nonneg d) (norm_nonneg x)
  simpa [abs_of_nonneg ha, abs_of_nonneg hb] using habs

/-- **对角算子范数下界**：`ρ̂(d) ≤ ‖matCLME (diag d)‖`。
取极大分量指标 `i₀`，在单位向量 `e_{i₀}` 上取到 `|d i₀| = ρ̂(d)`。 -/
theorem le_opNorm_diagonal (d : Fin n → ℝ) :
    diagRadius d ≤ ‖matCLME (Matrix.diagonal d)‖ := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    (H := Finset.univ_nonempty) (f := fun i => |d i|)
  have hle := (matCLME (Matrix.diagonal d)).le_opNorm (EuclideanSpace.single i₀ (1 : ℝ))
  rw [matCLME_apply, diagonal_eigenpair (d := d) (i := i₀)] at hle
  have hnorm : ‖d i₀ • EuclideanSpace.single i₀ (1 : ℝ)‖ = |d i₀| := by
    rw [norm_smul, Real.norm_eq_abs]
    simp
  have hnorm2 : ‖EuclideanSpace.single i₀ (1 : ℝ)‖ = (1 : ℝ) := by simp
  rw [hnorm, hnorm2, mul_one] at hle
  rw [show diagRadius d = |d i₀| from hi₀]
  exact hle

/-- **对角算子范数恒等式**：`‖matCLME (diag d)‖ = ρ̂(d)`（对角矩阵的范数 = 最大模）。 -/
theorem opNorm_diagonal (d : Fin n → ℝ) :
    ‖matCLME (Matrix.diagonal d)‖ = diagRadius d :=
  le_antisymm (opNorm_diagonal_le d) (le_opNorm_diagonal d)

/-! ## 五、对角情形的 Gelfand 公式 -/

/-- 对角矩阵的幂仍是对角矩阵，其算子范数 = 谱半径的幂。 -/
theorem opNorm_diagonal_pow (d : Fin n → ℝ) (k : ℕ) :
    ‖matCLME ((Matrix.diagonal d) ^ k)‖ = (diagRadius d) ^ k := by
  rw [Matrix.diagonal_pow, opNorm_diagonal]
  exact diagRadius_pow d k

/-- 实指数幂恒等式：`0 ≤ x`、`k ≠ 0` 时 `(x^k)^{1/k} = x`
（`Real.rpow_natCast` + `Real.rpow_mul` + `mul_one_div_cancel`）。 -/
theorem rpow_pow_one_div_natCast {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≠ 0) :
    (x ^ k) ^ (1 / (k : ℝ)) = x := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_mul hx]
  rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr hk), Real.rpow_one]

/-- **对角的 Gelfand 公式**：`‖(diag d)^k‖^{1/k} → ρ̂(d)`
（在 `k ≥ 1` 上该序列恒等于 `ρ̂(d)`，故极限为常数序列的极限）。 -/
theorem gelfand_diagonal (d : Fin n → ℝ) :
    Filter.Tendsto (fun k : ℕ => ‖matCLME ((Matrix.diagonal d) ^ k)‖ ^ (1 / (k : ℝ)))
      Filter.atTop (nhds (diagRadius d)) := by
  have heq : (fun k : ℕ => ‖matCLME ((Matrix.diagonal d) ^ k)‖ ^ (1 / (k : ℝ)))
      =ᶠ[Filter.atTop] (fun _ : ℕ => diagRadius d) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
    rw [opNorm_diagonal_pow]
    exact rpow_pow_one_div_natCast (diagRadius_nonneg d) (by omega)
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

/-! ## 六、一维特例（`Fin 1`） -/

section FinOne

/-- `Fin 1` 的非空实例（`Fin 1` 是单点型；用于上文的 `diagRadius`）。

⚠ **作用域更正（v14，S8 扫描发现）**：本节 `section FinOne` **不限制本实例的作用域**——
**Lean 的 `section` 只约束 `variable` 声明，不约束 `instance`/`theorem` 等声明本身**。
⇒ 本实例实为**全局** `Lattice.instNonemptyFinOne`，会**泄漏给所有 importer**
（如需真正限制在局部，必须写成 `letI`/`haveI`，或放进 `namespace` 并加 `private`）。
**保留不改名的理由**：本文件后续定理依赖它，删除需改动多处；
但**"仅在本节内"这一措辞是错的**，已按事实更正。
⚠ 另注：Mathlib 已有 `inhabitedFinOneAdd` 覆盖同类需求，本实例属**平行定义**。 -/
instance instNonemptyFinOne : Nonempty (Fin 1) := ⟨0⟩

/-- 一维对角谱半径：`ρ̂(d) = |d₀|`。 -/
theorem diagRadius_one (d : Fin 1 → ℝ) : diagRadius d = |d 0| := by
  apply le_antisymm
  · rw [diagRadius]
    refine (Finset.sup'_le_iff Finset.univ_nonempty (fun i : Fin 1 => |d i|)).mpr ?_
    intro b _
    rw [Fin.eq_zero b]
  · exact abs_le_diagRadius d 0

end FinOne

/-- 对角收敛条件：`ρ̂(d) < 1 ⟹ ‖matCLME (diag d)‖ < 1`（Neumann 级数前提）。 -/
theorem opNorm_diagonal_lt_one (d : Fin n → ℝ) (h : diagRadius d < 1) :
    ‖matCLME (Matrix.diagonal d)‖ < 1 := by
  rwa [opNorm_diagonal]

/-! ## 七、注：诚实降级
  · 只完成**对角矩阵**的谱半径刻画与 Gelfand 公式；**一般算子的 `ρ(T) ≤ ‖T‖` 与
    `ρ(T) = inf ‖Tᵏ‖^{1/k}` 已由 `RealGelfand` 补出**（任意实方阵，非对角）；
    **等号 `ρ(Tⁿ) = ρ(T)ⁿ` 仍未证**，根因是 Gelfand 极限定理需要**复 Banach 代数语境**
    （该定理 mathlib 4.14 **已有**：`Spectrum.lean:374`；本仓库未做复化适配）；
  · **复谱**：非实特征值（复共轭对）已由 `RealComplexSpectral` 补出；
  · `diagRadius` 只能在 `Nonempty (Fin n)`（等价 `n ≠ 0`）下定义，空维数被**降级**排除；
  · 未做：对称矩阵的 `ρ = ‖A‖` 完整谱定理路线、幂法收敛速率。 -/

end Lattice
