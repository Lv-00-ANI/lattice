import Mathlib
import Lattice.Lib.Optim.RealPolicyGradient
/-!
# LATTICE: Fisher 信息与自然梯度 —— 非负性、score 均值为零、二阶导数归约、最速下降

信息论/优化的交界（衔接 RealPolicyGradient 的 log 导数恒等式）：

一维参数 θ ∈ ℝ 的有限分布族 `p : ℝ → Fin k → ℝ`（每个 θ 处是概率向量）。
**score 函数**与 **Fisher 信息**：

    score_p,θ(a) = ∂_θ log p_θ(a)        （对数似然关于参数的导数）
    F(θ) = E_{p_θ}[(∂_θ log p_θ)²] = Σ_a p_θ(a)·score_p,θ(a)²

本文件建立：

  1. `score` / `fisherInfo`（定义）；
  2. `fisher_nonneg`：F(θ) ≥ 0（逐项非负）；
  3. `score_log_derivative`：0 < p_θ(a) 且可导 ⟹ ∂_θ p_θ(a) = p_θ(a)·score_p,θ(a)
     —— 即 log 导数恒等式（RealPolicyGradient.log_derivative_identity）的坐标形式；
  4. `fisher_score_mean_zero`（**完全可证**）：若 p_t 恒为概率向量（Σ_a p_t(a) ≡ 1）、
     p_θ > 0、各坐标在 θ 可导，则 Σ_a p_θ(a)·score_p,θ(a) = 0
     —— score 函数的期望为零（Fisher 信息的「一阶矩」性质）；
  5. `fisher_equals_second_derivative`（**一维 F = −E[d²log p]**，代数归约）：
     在链式法则的二阶形式 `(log p_θ)'' = p_θ''/p_θ − (score)²` 与 `Σ_a p_θ''(a) = 0`
     两条显式假设下，F(θ) = −Σ_a p_θ(a)·(log p_θ(a))''；
  6. `naturalGradient` / `natural_gradient_maximizes_quadratic`（**最速下降刻画**）：
     v* = F⁻¹g（F > 0）唯一最大化二次型 `g·v − (F/2)·v²`；g = −∇J 时
     v* = −F⁻¹∇J 即自然梯度方向。严格等号刻画见
     `natural_gradient_maximizes_quadratic_iff`；
  7. `fisher_cramer_rao`（**Cramér–Rao 下界**）：无偏估计 T（`Σ_a p_t(a)·T(a) = t`）
     的方差满足 `1 ≤ F(θ)·Σ_a p_θ(a)·(T a − θ)²`，即 Var(T) ≥ 1/F(θ)。
     证明：score 表示 `∂_θp = p·score` 与 Fisher 均值零把 `Σ p·score·(T−θ)` 化为
     ψ'(θ) = 1，再由加权 Cauchy–Schwarz 得界。

**诚实边界**（本文件不证 / 不声称的）：

- `fisher_equals_second_derivative` 的 `hsecond`（链式法则的二阶形式
  `(log p)'' = p''/p − (p'/p)²`）与 `hsum_second`（`Σ_a p_θ''(a) = 0`，即 Σp ≡ 1 的二阶导数）
  是**显式分析假设**：本定理给出 Fisher 信息的代数归约，二阶导数的存在性与
  「导数可与有限求和交换」未从零构造（照 RealPolicyGradient 中 `hlog` 的诚实风格）。
- `fisher_cramer_rao` 的 `hderivT`（`∂_θ Σ_a p_t(a)·T(a) = Σ_a (∂_θ p_t(a))·T(a)`，
  即导数与有限和交换）同样是显式假设；`hunit` 是把「T 的期望恒等于 θ」
  微分一次后的形式（ψ'(θ) = 1）。这两条在 p 各坐标可导时由 `deriv_sum` 与
  常数函数的导数自动给出。
- 未做：多参数（矩阵 Fisher / Fisher 度量）版本、Fisher 的 Cramér–Rao 等号刻画
  （指数族）、Fisher 信息与 KL 的二阶展开联系、自然梯度的收敛性。

模型无关：任意有限 k。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 定义：score 函数与 Fisher 信息 -/

/-- score 函数：score_p,θ(a) = ∂_θ log p_θ(a)。 -/
noncomputable def score (p : ℝ → Fin k → ℝ) (θ : ℝ) (a : Fin k) : ℝ :=
  deriv (fun t => Real.log (p t a)) θ

/-- Fisher 信息（一维参数）：F(θ) = Σ_a p_θ(a)·score_p,θ(a)²。 -/
noncomputable def fisherInfo (p : ℝ → Fin k → ℝ) (θ : ℝ) : ℝ :=
  ∑ a, p θ a * (score p θ a) ^ 2

/-! ## 定理一：Fisher 信息非负 -/

theorem fisher_nonneg (p : ℝ → Fin k → ℝ) (θ : ℝ) (hp : ∀ a, 0 ≤ p θ a) :
    0 ≤ fisherInfo p θ := by
  unfold fisherInfo
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (sq_nonneg _))

/-! ## 定理二：log 导数恒等式（坐标形式） -/

theorem score_log_derivative (p : ℝ → Fin k → ℝ) (θ : ℝ) (a : Fin k) (hpos : 0 < p θ a)
    (hd : DifferentiableAt ℝ (fun t => p t a) θ) :
    deriv (fun t => p t a) θ = p θ a * score p θ a :=
  log_derivative_identity (fun t => p t a) θ hpos hd

/-! ## 定理三：score 的期望为零

Σ_a p_t(a) ≡ 1 的两边对 t 求导：左边 = Σ_a ∂_t p_t(a)（导数与有限和交换），
用 log 导数恒等式换成 Σ_a p_t(a)·score_p,t(a)；右边 = 0。 -/

theorem fisher_score_mean_zero (p : ℝ → Fin k → ℝ) (θ : ℝ)
    (hsum : ∀ t, ∑ a, p t a = 1)
    (hpos : ∀ a, 0 < p θ a)
    (hd : ∀ a, DifferentiableAt ℝ (fun t => p t a) θ) :
    ∑ a, p θ a * score p θ a = 0 := by
  have hconst : (fun t : ℝ => ∑ a, p t a) = fun _ => (1 : ℝ) := by
    funext t
    exact hsum t
  have hderiv0 : deriv (fun t : ℝ => ∑ a, p t a) θ = 0 := by
    rw [hconst]
    simp
  have hsumderiv : deriv (fun t : ℝ => ∑ a, p t a) θ
      = ∑ a, deriv (fun t : ℝ => p t a) θ :=
    deriv_sum (u := Finset.univ) (A := fun a (t : ℝ) => p t a)
      (by intro a _; exact hd a)
  have hper : ∀ a, deriv (fun t : ℝ => p t a) θ = p θ a * score p θ a :=
    fun a => score_log_derivative p θ a (hpos a) (hd a)
  rw [hsumderiv] at hderiv0
  rw [Finset.sum_congr rfl (fun a _ => hper a)] at hderiv0
  exact hderiv0

/-! ## 定理四：Fisher = −E[d²log p]（一维，代数归约）

在 hsecond（(log p)'' = p''/p − (p'/p)²）与 hsum_second（Σ p'' = 0）下：
−Σ_a p_θ(a)·(log p_θ(a))'' = −Σ_a (p_θ''(a) − p_θ(a)·score²) = Σ_a p_θ(a)·score² = F(θ)。 -/

theorem fisher_equals_second_derivative (p : ℝ → Fin k → ℝ) (θ : ℝ)
    (hp : ∀ a, 0 < p θ a)
    (hsecond : ∀ a, deriv (fun t => deriv (fun s => Real.log (p s a)) t) θ
        = deriv (fun t => deriv (fun s => p s a) t) θ / p θ a - (score p θ a) ^ 2)
    (hsum_second : ∑ a, deriv (fun t => deriv (fun s => p s a) t) θ = 0) :
    fisherInfo p θ
      = -∑ a, p θ a * deriv (fun t => deriv (fun s => Real.log (p s a)) t) θ := by
  have hterm : ∀ a, p θ a * deriv (fun t => deriv (fun s => Real.log (p s a)) t) θ
      = deriv (fun t => deriv (fun s => p s a) t) θ - p θ a * (score p θ a) ^ 2 := by
    intro a
    rw [hsecond a]
    field_simp [ne_of_gt (hp a)]
  have hS3 : ∑ a, p θ a * deriv (fun t => deriv (fun s => Real.log (p s a)) t) θ
      = ∑ a, (deriv (fun t => deriv (fun s => p s a) t) θ
          - p θ a * (score p θ a) ^ 2) :=
    Finset.sum_congr rfl (fun a _ => hterm a)
  have hsplit : ∑ a, (deriv (fun t => deriv (fun s => p s a) t) θ
        - p θ a * (score p θ a) ^ 2)
      = ∑ a, deriv (fun t => deriv (fun s => p s a) t) θ
        - ∑ a, p θ a * (score p θ a) ^ 2 :=
    Finset.sum_sub_distrib
  unfold fisherInfo
  linarith [hS3, hsplit, hsum_second]

/-! ## 定义与定理五：自然梯度与最速下降刻画 -/

/-- 自然梯度（一维）：F⁻¹·g。 -/
noncomputable def naturalGradient (F g : ℝ) : ℝ := g / F

/-- 配方法（二次型的完全平方）。 -/
lemma quad_complete_square (F g v : ℝ) (hF : F ≠ 0) :
    g * v - (F / 2) * v ^ 2 = g ^ 2 / (2 * F) - (F / 2) * (v - g / F) ^ 2 := by
  field_simp [hF]
  ring

/-- 自然梯度处的二次型值。 -/
lemma quad_at_naturalGradient (F g : ℝ) (hF : F ≠ 0) :
    g * (naturalGradient F g) - (F / 2) * (naturalGradient F g) ^ 2 = g ^ 2 / (2 * F) := by
  unfold naturalGradient
  field_simp [hF]
  ring

/-- 自然梯度是 Fisher 度量下二次型的最速下降方向：
F > 0 时 v* = g/F 最大化 v ↦ g·v − (F/2)·v²。
g = −∇J 时「最大化 g·v − (F/2)v²」即「最小化 ∇J·v + (F/2)v²」，
即 Fisher 度量 ‖v‖²_F = F·v² 下的最速下降。 -/
theorem natural_gradient_maximizes_quadratic (F g : ℝ) (hF : 0 < F) :
    ∀ v : ℝ,
      g * v - (F / 2) * v ^ 2
        ≤ g * (naturalGradient F g) - (F / 2) * (naturalGradient F g) ^ 2 := by
  intro v
  have hFne : F ≠ 0 := ne_of_gt hF
  rw [quad_complete_square F g v hFne, quad_at_naturalGradient F g hFne]
  have hnn : 0 ≤ (F / 2) * (v - g / F) ^ 2 :=
    mul_nonneg (div_nonneg (le_of_lt hF) (by norm_num)) (sq_nonneg _)
  linarith

/-- 最速下降刻画的等号情形：二次型取到最大值 ⟺ v 恰是自然梯度 v* = g/F。 -/
theorem natural_gradient_maximizes_quadratic_iff (F g : ℝ) (hF : 0 < F) (v : ℝ) :
    (g * v - (F / 2) * v ^ 2
        = g * (naturalGradient F g) - (F / 2) * (naturalGradient F g) ^ 2)
      ↔ v = naturalGradient F g := by
  have hFne : F ≠ 0 := ne_of_gt hF
  have hF2 : (F / 2) ≠ 0 := by positivity
  rw [quad_complete_square F g v hFne, quad_at_naturalGradient F g hFne]
  constructor
  · intro h
    have hmul : (F / 2) * (v - g / F) ^ 2 = 0 := by linarith
    have hsq : (v - g / F) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hmul with h1 | h2
      · exact absurd h1 hF2
      · exact h2
    have hv : v - g / F = 0 := pow_eq_zero hsq
    unfold naturalGradient
    linarith
  · intro h
    rw [h]
    unfold naturalGradient
    ring

/-! ## 定理六：Cramér–Rao 下界

无偏估计 T（ψ(θ) = Σ_a p_θ(a)·T(a)，ψ'(θ) = 1）的方差满足
1 ≤ F(θ)·Σ_a p_θ(a)·(T a − θ)²，即 Var(T) ≥ 1/F(θ)。
证明：加权 Cauchy–Schwarz
(Σ p·score·(T−θ))² ≤ (Σ p·score²)(Σ p·(T−θ)²)，
左边由 score 表示与 Fisher 均值零化为 ψ'(θ)² = 1。 -/

theorem fisher_cramer_rao (p : ℝ → Fin k → ℝ) (T : Fin k → ℝ) (θ : ℝ)
    (hp : ∀ a, 0 < p θ a)
    (hd : ∀ a, DifferentiableAt ℝ (fun t => p t a) θ)
    (hscore : ∑ a, p θ a * score p θ a = 0)
    (hderivT : deriv (fun t => ∑ a, p t a * T a) θ
      = ∑ a, deriv (fun t => p t a) θ * T a)
    (hunit : deriv (fun t => ∑ a, p t a * T a) θ = 1) :
    1 ≤ fisherInfo p θ * ∑ a, p θ a * (T a - θ) ^ 2 := by
  have hlog : ∀ a, deriv (fun t => p t a) θ = p θ a * score p θ a :=
    fun a => score_log_derivative p θ a (hp a) (hd a)
  have h1 : ∑ a, p θ a * score p θ a * T a = 1 := by
    have hEq : ∑ a, p θ a * score p θ a * T a
        = ∑ a, deriv (fun t => p t a) θ * T a :=
      Finset.sum_congr rfl (fun a _ => by rw [hlog a])
    rw [hEq, ← hderivT]
    exact hunit
  have h2 : ∑ a, p θ a * score p θ a * (T a - θ) = 1 := by
    have hsplit : ∑ a, p θ a * score p θ a * (T a - θ)
        = ∑ a, p θ a * score p θ a * T a
          - ∑ a, p θ a * score p θ a * θ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have htheta : ∑ a, p θ a * score p θ a * θ = θ * ∑ a, p θ a * score p θ a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hsplit, h1, htheta, hscore, mul_zero, sub_zero]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun a => Real.sqrt (p θ a) * score p θ a)
    (g := fun a => Real.sqrt (p θ a) * (T a - θ))
  have hx : ∑ a, Real.sqrt (p θ a) * score p θ a * (Real.sqrt (p θ a) * (T a - θ)) = 1 := by
    have hper : ∀ a, Real.sqrt (p θ a) * score p θ a * (Real.sqrt (p θ a) * (T a - θ))
        = p θ a * score p θ a * (T a - θ) := by
      intro a
      rw [show Real.sqrt (p θ a) * score p θ a * (Real.sqrt (p θ a) * (T a - θ))
          = (Real.sqrt (p θ a) * Real.sqrt (p θ a)) * (score p θ a * (T a - θ)) by ring,
        Real.mul_self_sqrt (le_of_lt (hp a))]
      ring
    rw [Finset.sum_congr rfl (fun a _ => hper a), h2]
  have hxx : ∑ a, (Real.sqrt (p θ a) * score p θ a) ^ 2 = fisherInfo p θ := by
    unfold fisherInfo
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hp a))]
  have hyy : ∑ a, (Real.sqrt (p θ a) * (T a - θ)) ^ 2
      = ∑ a, p θ a * (T a - θ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hp a))]
  rw [hx, hxx, hyy] at hcs
  linarith

end Lattice
