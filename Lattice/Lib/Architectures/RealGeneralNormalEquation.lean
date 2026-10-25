import Mathlib
import Lattice.Lib.Architectures.RealNormalEquation
/-!
# LATTICE: 通用法方程 —— probe 最优性（无需一致性假设）

提取调研（research/real-world/extraction-math.md §3 性质一）：
`RealNormalEquation.P0_normal_equation`（`RealNormalEquation.lean`，`A : E →L[ℝ] F`）
要求一致系统（b ∈ range A）；真实数据（线性探针）
常态是**不一致**（残差非零）。去掉一致性假设的推广：

  fderiv (‖A·x - b‖²) x = 0  ⟺  ∀ v, ⟨A·x - b, A·v⟩ = 0

即「驻点 ⟺ 残差正交于 A 的值域」（法方程 Xᵀ(Xw̃−y) = 0 的抽象形式）。
这是线性探针最优性的刻画：最小二乘解 = 驻点，不要求标签线性可分。

证明复用 RealNormalEquation 的前半段（fderiv → 方向导数 → 正交），
反向由 fderiv_loss_apply 直接给出。
-/


noncomputable section

open Filter
open scoped Topology

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ## 定理：通用法方程 —— 驻点 ⟺ 残差正交于值域
fderiv (‖Ax-b‖²) x = 0 ⟺ ∀ v, ⟨Ax-b, Av⟩ = 0（无一致性假设）。-/

theorem fderiv_loss_zero_iff_orthogonal (A : E →L[ℝ] F) (b : F) (x : E) :
    fderiv ℝ (NormSqLoss A b) x = 0 ↔ ∀ v : E, inner (A x - b) (A v) = (0 : ℝ) := by
  constructor
  · intro hfd v
    -- fderiv = 0 ⟹ 方向导数 = 0
    have hz : fderiv ℝ (NormSqLoss A b) x v = 0 :=
      (fderiv_eq_zero_iff_all (NormSqLoss A b) x (loss_differentiable A b x)).mp hfd v
    -- 方向导数 = 2⟨Ax-b, Av⟩ = 0
    have h2 : 2 * inner (A x - b) (A v) = (0 : ℝ) := by
      rwa [fderiv_loss_apply A b x v] at hz
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
  · intro h
    rw [fderiv_eq_zero_iff_all (NormSqLoss A b) x (loss_differentiable A b x)]
    intro v
    rw [fderiv_loss_apply A b x v]
    simp [h v]

/-! ## 推论一：一致系统 ⟹ 法方程即满足（衔接 P0_normal_equation）
若 b ∈ range A 且驻点，则残差正交且残差在值域内 ⟹ 残差 = 0（Ax = b）。
-/

theorem normal_eq_consistent (A : E →L[ℝ] F) (b : F) (x : E)
    (hb : b ∈ LinearMap.range (A : E →ₗ[ℝ] F))
    (hfd : fderiv ℝ (NormSqLoss A b) x = 0) :
    A x = b := by
  exact (P0_normal_equation A b x hb).mp hfd

/-! ## 推论二：不一致系统的解集刻画
驻点集 = 法方程解集 = {x | ∀v, ⟨Ax-b, Av⟩=0}（最小二乘解，残差正交）。
-/

theorem stationarity_eq_normal_equation_solutions (A : E →L[ℝ] F) (b : F) :
    {x : E | fderiv ℝ (NormSqLoss A b) x = 0} =
    {x : E | ∀ v : E, inner (A x - b) (A v) = (0 : ℝ)} := by
  ext x
  exact fderiv_loss_zero_iff_orthogonal A b x

/-! ## 推论三：驻点间残差常数
任意两个驻点 x₁ x₂：A·x₁ = A·x₂（值域内相同投影）——最小二乘解共享同一拟合。
-/

theorem stationarity_same_fit (A : E →L[ℝ] F) (b : F) (x₁ x₂ : E)
    (h₁ : fderiv ℝ (NormSqLoss A b) x₁ = 0)
    (h₂ : fderiv ℝ (NormSqLoss A b) x₂ = 0) :
    A x₁ = A x₂ := by
  -- 两个驻点 → 残差都正交值域 → r₁ - r₂ 正交值域且在值域内
  have hor₁ : ∀ v, inner (A x₁ - b) (A v) = (0 : ℝ) := (fderiv_loss_zero_iff_orthogonal A b x₁).mp h₁
  have hor₂ : ∀ v, inner (A x₂ - b) (A v) = (0 : ℝ) := (fderiv_loss_zero_iff_orthogonal A b x₂).mp h₂
  -- 残差差：r₁ - r₂ = A(x₁-x₂) ∈ range A；且正交值域
  have hdiff_in_range : A x₁ - A x₂ ∈ LinearMap.range (A : E →ₗ[ℝ] F) := by
    exact LinearMap.mem_range.mpr ⟨x₁ - x₂, by simp⟩
  have hdiff_orth : A x₁ - A x₂ ∈ Submodule.orthogonal (LinearMap.range (A : E →ₗ[ℝ] F)) := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rcases (LinearMap.mem_range.mp hy) with ⟨v, rfl⟩
    -- ⟨A x₁ - A x₂, A v⟩ = ⟨A v, A x₁ - A x₂⟩（实内积对称）⟹ ⟨A x₁, A v⟩ - ⟨A x₂, A v⟩
    rw [real_inner_comm]
    rw [inner_sub_left]
    change inner (A x₁) (A v) - inner (A x₂) (A v) = (0 : ℝ)
    have hb₁ : (inner (A x₁) (A v) : ℝ) = (inner (A x₁ - b) (A v) + inner b (A v) : ℝ) := by
      rw [← inner_add_left]
      congr 1
      abel
    have hb₂ : (inner (A x₂) (A v) : ℝ) = (inner (A x₂ - b) (A v) + inner b (A v) : ℝ) := by
      rw [← inner_add_left]
      congr 1
      abel
    rw [hb₁, hb₂, hor₁ v, hor₂ v]
    ring
  -- 交集为 ⊥ → 残差差 = 0 → A x₁ = A x₂
  have hbot : A x₁ - A x₂ = 0 := by
    have hmem : A x₁ - A x₂ ∈
        (LinearMap.range (A : E →ₗ[ℝ] F)) ⊓
        (Submodule.orthogonal (LinearMap.range (A : E →ₗ[ℝ] F))) :=
      Submodule.mem_inf.mpr ⟨hdiff_in_range, hdiff_orth⟩
    have hdisj : (LinearMap.range (A : E →ₗ[ℝ] F)) ⊓
        (Submodule.orthogonal (LinearMap.range (A : E →ₗ[ℝ] F))) = ⊥ := by
      exact Submodule.inf_orthogonal_eq_bot (LinearMap.range (A : E →ₗ[ℝ] F))
    have : A x₁ - A x₂ ∈ (⊥ : Submodule ℝ F) := by simpa [hdisj] using hmem
    simpa using this
  exact sub_eq_zero.mp hbot

end Lattice
