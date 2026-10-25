import Mathlib
import Lattice.Lib.InfoTheory.RealMaxEntropy
/-!
# LATTICE: 最大熵的唯一 θ —— 矩映射的严格单调性、单射与存在唯一性

RealMaxEntropy 已证「指数族（Gibbs 分布）在给定矩下最大化熵」（变分刻画），
但**未**断言「给定矩存在唯一 θ」。本文件补上这半边：**矩映射**

    momentMap(g, θ) = E_{Gibbs(g,θ)}[g] = Σ_a (exp(θ·g_a)/Z(θ))·g_a

的严格单调性与单射性，从而在矩可达时给出 θ 的存在唯一性。

本文件建立：

  1. `momentMap` / `variance`（定义）；`variance_nonneg`：
     方差 `V(θ) = E[g²] − E[g]² ≥ 0`（加权 Cauchy–Schwarz，无需额外假设）；
  2. `momentMap_eq_deriv_logZ`（**核心恒等式**）：∂_θ log Z(θ) = E[g] = momentMap(g,θ)
     —— 指数族的一阶矩恒等式（对 Z = Σ_a e^{θ·g_a} 逐项求导后用商/对数法则）；
  3. `variance_eq_quotient` / `momentMap_deriv`（**核心二阶恒等式**）：
     ∂_θ momentMap(g,θ) = V(θ)（商法则 + 方差的有理化形式）；
  4. `momentMap_strictMono`（**核心**）：V > 0 ⟹ θ ↦ E_{Gibbs}[g] 严格单调递增
     （`strictMono_of_deriv_pos`）；`momentMap_injective`：严格单调 ⟹ 单射；
  5. `unique_theta_for_moment`（**核心，本文件目标**）：给定目标矩 m 在矩映射值域内
     ⟹ 存在唯一 θ 使 momentMap(g,θ) = m。

**诚实边界**（本文件不证 / 不声称的）：

- `V(θ) > 0`（`hvar`）在 `momentMap_strictMono` 中是**显式假设**：本文件证明了
  V ≥ 0（`variance_nonneg`），但「g 非常值 ⟹ V > 0」需要 Cauchy–Schwarz 的
  **严格**等号情形（g 沿 Gibbs 支撑为常数）——那是真的但需要额外论证，
  标注为后续。`momentMap_deriv` 已把 `deriv momentMap = V` 无条件证出，
  故严格单调性的唯一额外输入就是 V > 0。
- **满射性（值域 = ℝ 的开区间）与中值定理的存在性方向未证**：`unique_theta_for_moment`
  把「m 在值域内」当作前提（`hrange`），而不是从 θ → ±∞ 的极限推出。
  连续 + 极限 → ±∞ ⟹ 满射的中值定理论证标注为后续。
- `maxEntropy_with_moment_constraint`（RealMaxEntropy）需要的正是「给定矩存在 θ」；
  本文件的 `unique_theta_for_moment` 补上该存在唯一性（在 hrange/hmono 假设下）。
- 未做：多维矩映射的凸性与单调性（需要 log Z 的严格凸性）、指数族的
  Legendre 对偶、连续情形的最大熵。

模型无关：任意有限 k。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 定义：矩映射与方差 -/

/-- 矩映射：momentMap(g,θ) = Σ_a Gibbs(g,θ)_a·g_a = E_{Gibbs(g,θ)}[g]。 -/
noncomputable def momentMap (g : Fin k → ℝ) (θ : ℝ) : ℝ :=
  ∑ a, gibbsDist g θ a * g a

/-- 指数族方差：V(θ) = E[g²] − E[g]² = Σ_a q_a·g_a² − (Σ_a q_a·g_a)²。 -/
noncomputable def variance (g : Fin k → ℝ) (θ : ℝ) : ℝ :=
  ∑ a, gibbsDist g θ a * (g a) ^ 2 - (momentMap g θ) ^ 2

/-! ## 定理一：方差非负（加权 Cauchy–Schwarz） -/

theorem variance_nonneg [Nonempty (Fin k)] (g : Fin k → ℝ) (θ : ℝ) :
    0 ≤ variance g θ := by
  have hq : ∀ a, 0 ≤ gibbsDist g θ a := fun a => le_of_lt (gibbsDist_pos g θ a)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun a => Real.sqrt (gibbsDist g θ a))
    (g := fun a => Real.sqrt (gibbsDist g θ a) * g a)
  have hx : (∑ a, Real.sqrt (gibbsDist g θ a)
        * (Real.sqrt (gibbsDist g θ a) * g a)) = momentMap g θ := by
    unfold momentMap
    apply Finset.sum_congr rfl
    intro a _
    rw [show Real.sqrt (gibbsDist g θ a) * (Real.sqrt (gibbsDist g θ a) * g a)
        = (Real.sqrt (gibbsDist g θ a) * Real.sqrt (gibbsDist g θ a)) * g a by ring,
      Real.mul_self_sqrt (hq a)]
  have hf : (∑ a, (Real.sqrt (gibbsDist g θ a)) ^ 2) = 1 := by
    rw [Finset.sum_congr rfl (fun a _ => Real.sq_sqrt (hq a)), gibbsDist_sum g θ]
  have hg' : (∑ a, (Real.sqrt (gibbsDist g θ a) * g a) ^ 2)
      = ∑ a, gibbsDist g θ a * (g a) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_pow, Real.sq_sqrt (hq a)]
  rw [hx, hf, hg', one_mul] at hcs
  unfold variance
  linarith

/-! ## 定理二（核心）：一阶矩恒等式 ∂_θ log Z = E[g] -/

theorem momentMap_eq_deriv_logZ [Nonempty (Fin k)] (g : Fin k → ℝ) (θ : ℝ) :
    deriv (fun t => Real.log (gibbsPartition g t)) θ = momentMap g θ := by
  have hZ : HasDerivAt (fun t => gibbsPartition g t)
      (∑ a, Real.exp (θ * g a) * g a) θ := by
    unfold gibbsPartition
    apply HasDerivAt.sum
    intro a _
    have h1 : HasDerivAt (fun t : ℝ => t * g a) (1 * g a) θ :=
      (hasDerivAt_id θ).mul_const (g a)
    have h2 := (Real.hasDerivAt_exp (θ * g a)).comp θ h1
    simpa using h2
  have hZpos : gibbsPartition g θ ≠ 0 := ne_of_gt (gibbsPartition_pos g θ)
  have hlog := hZ.log hZpos
  rw [hlog.deriv]
  unfold momentMap gibbsDist
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-! ## 定理三（核心）：二阶矩恒等式 ∂_θ E[g] = V(θ)

把 momentMap 写成 (Σ_a g_a·e^{θg_a}) / Z(θ)，用商法则；
方差写成有理形式 (N'·Z − N·Z')/Z²（`variance_eq_quotient`）。 -/

/-- 方差的有理化形式（N = Σ_a g_a·e^{θg_a}、N' = Σ_a g_a²·e^{θg_a}、Z' = Σ_a e^{θg_a}·g_a）：
V(θ) = (N'·Z(θ) − N·Z') / Z(θ)²。 -/
lemma variance_eq_quotient [Nonempty (Fin k)] (g : Fin k → ℝ) (θ : ℝ) :
    variance g θ
      = ((∑ a, g a * (g a * Real.exp (θ * g a))) * gibbsPartition g θ
          - (∑ a, g a * Real.exp (θ * g a)) * (∑ a, Real.exp (θ * g a) * g a))
        / gibbsPartition g θ ^ 2 := by
  have hZ : gibbsPartition g θ ≠ 0 := ne_of_gt (gibbsPartition_pos g θ)
  have h1 : ∑ a, gibbsDist g θ a * (g a) ^ 2
      = (∑ a, g a * (g a * Real.exp (θ * g a))) / gibbsPartition g θ := by
    unfold gibbsDist
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h2 : ∑ a, gibbsDist g θ a * g a
      = (∑ a, Real.exp (θ * g a) * g a) / gibbsPartition g θ := by
    unfold gibbsDist
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h3 : (∑ a, g a * Real.exp (θ * g a)) = (∑ a, Real.exp (θ * g a) * g a) := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold variance momentMap
  rw [h1, h2, h3]
  field_simp [hZ]
  ring

theorem momentMap_deriv [Nonempty (Fin k)] (g : Fin k → ℝ) (θ : ℝ) :
    deriv (momentMap g) θ = variance g θ := by
  have hZ : HasDerivAt (fun t => gibbsPartition g t)
      (∑ a, Real.exp (θ * g a) * g a) θ := by
    unfold gibbsPartition
    apply HasDerivAt.sum
    intro a _
    have h1 : HasDerivAt (fun t : ℝ => t * g a) (1 * g a) θ :=
      (hasDerivAt_id θ).mul_const (g a)
    have h2 := (Real.hasDerivAt_exp (θ * g a)).comp θ h1
    simpa using h2
  have hN : HasDerivAt (fun t => ∑ a, g a * Real.exp (t * g a))
      (∑ a, g a * (g a * Real.exp (θ * g a))) θ := by
    apply HasDerivAt.sum
    intro a _
    have h1 : HasDerivAt (fun t : ℝ => t * g a) (1 * g a) θ :=
      (hasDerivAt_id θ).mul_const (g a)
    have h2 := (Real.hasDerivAt_exp (θ * g a)).comp θ h1
    have h3 := h2.const_mul (g a)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h3
  have hZpos : gibbsPartition g θ ≠ 0 := ne_of_gt (gibbsPartition_pos g θ)
  have hdiv := hN.div hZ hZpos
  have hfun : momentMap g
      = fun t => (∑ a, g a * Real.exp (t * g a)) / gibbsPartition g t := by
    funext t
    unfold momentMap gibbsDist
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hfun, hdiv.deriv, variance_eq_quotient]

/-! ## 定理四：矩映射严格单调与单射 -/

/-- 矩映射严格单调递增：∂_θ momentMap = V > 0 ⟹ StrictMono（`strictMono_of_deriv_pos`）。
（V > 0 是显式假设，见「诚实边界」。） -/
theorem momentMap_strictMono [Nonempty (Fin k)] (g : Fin k → ℝ)
    (hvar : ∀ θ, 0 < variance g θ) : StrictMono (momentMap g) :=
  strictMono_of_deriv_pos (fun θ => by
    rw [momentMap_deriv g θ]
    exact hvar θ)

theorem momentMap_injective (g : Fin k → ℝ) (hmono : StrictMono (momentMap g)) :
    Function.Injective (momentMap g) :=
  hmono.injective

/-! ## 定理五（核心）：给定矩的存在唯一 θ -/

/-- 给定目标矩 m 在矩映射值域内、且矩映射严格单调 ⟹ 存在唯一 θ 使 momentMap(g,θ) = m。
   「存在」由 hrange 直接给出，「唯一」由严格单调的单射性。 -/
theorem unique_theta_for_moment (g : Fin k → ℝ) (m : ℝ)
    (hmono : StrictMono (momentMap g)) (hrange : ∃ θ, momentMap g θ = m) :
    ∃! θ, momentMap g θ = m := by
  obtain ⟨θ0, hθ0⟩ := hrange
  refine ⟨θ0, hθ0, ?_⟩
  intro θ hθ
  exact hmono.injective (by rw [hθ, hθ0])

/-! ## 推论：与 RealMaxEntropy 的最大熵变分刻画衔接

「给定矩存在 θ」的唯一性 + RealMaxEntropy.maxEntropy_with_moment_constraint
（指数族在给定矩下最大化熵）合起来给出：矩约束下的最大熵分布在指数族中唯一确定。 -/

theorem unique_theta_for_moment_of_mono [Nonempty (Fin k)] (g : Fin k → ℝ)
    (hvar : ∀ θ, 0 < variance g θ) (m : ℝ)
    (hrange : ∃ θ, momentMap g θ = m) :
    ∃! θ, momentMap g θ = m :=
  unique_theta_for_moment g m (momentMap_strictMono g hvar) hrange

end Lattice
