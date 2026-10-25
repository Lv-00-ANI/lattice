import Mathlib
import Lattice.Lib.LearningTheory.RealSamplingBoost
import Lattice.Lib.InfoTheory.RealFDivergence
/-!
# LATTICE: 重要性采样 —— 分布变换的无偏性与方差界

方向（§5 验证行「重要性采样 / 分布变换」）：RealSamplingBoost 给出「同一
分布上多轮独立采样」的置信度放大（P(miss) ≤ ε ⟹ P(k 轮全 miss) ≤ ε^k）；
RealRandomVerify 的 `verify_probability_guarantee` 要求能从目标分布采样。
本文件处理**不能直接从目标分布采样**的情形：用提议分布 q 采样、以权重
p/q 校正，构造目标分布 p 下期望的无偏估计量，并给出其方差与提议分布
质量的关系（χ² 散度衔接 RealFDivergence）。

**设定（有限计数概率空间，k 个点上的两个分布 p、q）**：
目标分布 p : Fin k → ℝ（Σp = 1，p ≥ 0）、提议分布 q > 0（Σq = 1，
允许 p 在 q 的正支撑上），被估函数 f : Fin k → ℝ。

  · 重要性权重 `isWeight p q a = p a / q a`；
  · 估计量 `isEstimator p q f a = (p a/q a)·f(a)`；
  · 估计量二阶矩（关于 q）`isSecondMoment p q f = Σ_a q_a·g(a)²`。

**定理链**：
1. `is_weight_nonneg`：p ≥ 0、q > 0 ⟹ 权重 p/q ≥ 0。
2. `is_unbiased`（核心无偏性）：Σ_a p_a·f(a) = Σ_a q_a·(p_a/q_a)·f(a)
   —— 用提议分布 q 的样本 + 权重 p/q 得到的期望估计无偏（q > 0）。
3. `is_second_moment_eq`：Σ_a q_a·((p_a/q_a)f_a)² = Σ_a p_a²f_a²/q_a。
4. `chiSq_eq_sum_sq_div`：χ²(q‖p)（RealFDivergence 的 `chiSq q p`
   = Σ_a q_a·(p_a/q_a − 1)²）= Σ_a p_a²/q_a − 1（Σp = Σq = 1）；即
   Σ_a p_a²/q_a = 1 + χ²(q‖p)。
5. `is_second_moment_const`：f ≡ 1 时 E_q[g²] = 1 + χ²(q‖p)
   —— 重要性采样的二阶矩由 χ² 散度精确控制。
6. `is_variance_bound`（核心方差界）：|f| ≤ B ⟹
   E_q[g²] ≤ B²·(1 + χ²(q‖p))；因 Var_q(g) = E_q[g²] − (E_p f)² ≤ E_q[g²]，
   该式即重要性采样估计量的方差界（方差随 χ² 散度线性增长）。
7. `is_optimal_q`（最优提议分布的刻画）：对**任意** q > 0（Σq = 1），
   E_q[g²] ≥ (E_p|f|)²，即二阶矩的下确界是 (Σ_a p_a|f(a)|)²；
   证明用 Engel 形式 Cauchy–Schwarz（`Finset.sq_sum_div_le_sum_sq_div`，
   Sedrakyan/Titu）取 f_a = p_a|f_a|、g_a = q_a。
8. `is_optimal_q_attained`（等式达到）：提议分布 q*(a) ∝ p_a·|f_a|
   （`isOptimalQ`，归一化 Z = Σ p|f| > 0）时 E_{q*}[g²] = Z²，
   达到定理 7 的下界 —— 这证明 q* ∝ p·|f| 是**方差最优**提议分布。
   诚实标注：定理 7 的下界对任意 q 成立、定理 8 证明 q* 达到它，二者合并
   即最优性；但 q* 的一般构造要求 p_a|f_a| > 0 处处（否则需先剔除
   零质量点，此处显式假设）。

诚实假设：q > 0 处处（权重 p/q 有定义）、Σp = Σq = 1（概率归一）、
k > 0（定理 8 的归一化常数正）、|f| ≤ B（方差界的界）。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {k : ℕ}

/-! ## 定义：重要性权重与估计量 -/

/-- 重要性权重：用提议分布 q 的样本估计目标分布 p 下的期望时的权重 p_a/q_a。 -/
noncomputable def isWeight (p q : Fin k → ℝ) : Fin k → ℝ := fun a => p a / q a

/-- 重要性采样估计量：g(a) = (p_a/q_a)·f(a)。 -/
noncomputable def isEstimator (p q : Fin k → ℝ) (f : Fin k → ℝ) : Fin k → ℝ :=
  fun a => p a / q a * f a

/-- 最优（方差最小）提议分布：q*(a) ∝ p_a·|f(a)|，归一化常数为 Σ_a p_a|f(a)|。 -/
noncomputable def isOptimalQ (p f : Fin k → ℝ) : Fin k → ℝ :=
  fun a => p a * |f a| / (∑ b, p b * |f b|)

/-! ## 定理 1：重要性权重非负 -/

theorem is_weight_nonneg (p q : Fin k → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 < q a) :
    ∀ a, 0 ≤ isWeight p q a := by
  intro a
  unfold isWeight
  exact div_nonneg (hp a) (le_of_lt (hq a))

/-! ## 定理 2（核心）：无偏性
Σ_a p_a·f(a) = Σ_a q_a·(p_a/q_a)·f(a)。
证明：逐项 q_a·(p_a/q_a) = p_a（`mul_div_self`，RealFDivergence）。 -/

theorem is_unbiased (p q f : Fin k → ℝ) (hq : ∀ a, q a ≠ 0) :
    (∑ a, p a * f a) = ∑ a, q a * (p a / q a * f a) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc, mul_div_self (p a) (q a) (hq a)]

/-! ## 定理 3：二阶矩的显式形式
E_q[g²] = Σ_a q_a·((p_a/q_a)f_a)² = Σ_a p_a²·f_a²/q_a。 -/

theorem is_second_moment_eq (p q f : Fin k → ℝ) (hq : ∀ a, 0 < q a) :
    (∑ a, q a * (p a / q a * f a) ^ 2) = ∑ a, p a ^ 2 * f a ^ 2 / q a := by
  apply Finset.sum_congr rfl
  intro a _
  have hqa : q a ≠ 0 := ne_of_gt (hq a)
  field_simp [hqa]
  ring

/-! ## 定理 4：χ² 散度与 Σp²/q 的关系
χ²(q‖p) = Σ_a q_a·(p_a/q_a − 1)² = Σ_a p_a²/q_a − 1（Σp = Σq = 1）；
即 Σ_a p_a²/q_a = 1 + χ²(q‖p)。这正是 `chiSq`（RealFDivergence）的定义球。 -/

theorem chiSq_eq_sum_sq_div (p q : Fin k → ℝ) (hq : ∀ a, 0 < q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) :
    chiSq q p = (∑ a, p a ^ 2 / q a) - 1 := by
  unfold chiSq fDivergence
  calc
    (∑ a, q a * ((p a / q a) - 1) ^ 2) = ∑ a, (p a ^ 2 / q a - 2 * p a + q a) := by
      apply Finset.sum_congr rfl
      intro a _
      have hqa : q a ≠ 0 := ne_of_gt (hq a)
      field_simp [hqa]
      ring
    _ = (∑ a, p a ^ 2 / q a) - 2 * (∑ a, p a) + (∑ a, q a) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ a, p a ^ 2 / q a) - 1 := by rw [hp1, hq1]; ring

/-! ## 定理 5：常函数 f ≡ 1 时二阶矩 = 1 + χ²(q‖p) -/

theorem is_second_moment_const (p q : Fin k → ℝ) (hq : ∀ a, 0 < q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) :
    (∑ a, q a * (p a / q a * 1) ^ 2) = 1 + chiSq q p := by
  rw [is_second_moment_eq p q (fun _ => 1) hq]
  rw [chiSq_eq_sum_sq_div p q hq hp1 hq1]
  simp only [one_pow, mul_one]
  ring

/-! ## 定理 6（核心）：重要性采样的方差界（χ² 衔接）
|f| ≤ B、q > 0、Σp = Σq = 1 ⟹ E_q[g²] ≤ B²·(1 + χ²(q‖p))。
证明：定理 3 + 逐项 f_a² ≤ B²（`sq_le_sq'`）+ 定理 4 的 Σp²/q = 1 + χ²。 -/

theorem is_variance_bound (p q f : Fin k → ℝ) {B : ℝ} (hq : ∀ a, 0 < q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) (hf : ∀ a, |f a| ≤ B) :
    (∑ a, q a * (p a / q a * f a) ^ 2) ≤ B ^ 2 * (1 + chiSq q p) := by
  rw [is_second_moment_eq p q f hq]
  have hpt : ∀ a, p a ^ 2 * f a ^ 2 / q a ≤ B ^ 2 * (p a ^ 2 / q a) := by
    intro a
    have hf2 : f a ^ 2 ≤ B ^ 2 :=
      sq_le_sq' (abs_le.mp (hf a)).1 (abs_le.mp (hf a)).2
    calc
      p a ^ 2 * f a ^ 2 / q a ≤ p a ^ 2 * B ^ 2 / q a :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf2 (sq_nonneg _))
          (le_of_lt (hq a))
      _ = B ^ 2 * (p a ^ 2 / q a) := by ring
  calc
    (∑ a, p a ^ 2 * f a ^ 2 / q a) ≤ ∑ a, B ^ 2 * (p a ^ 2 / q a) :=
      Finset.sum_le_sum (fun a _ => hpt a)
    _ = B ^ 2 * (∑ a, p a ^ 2 / q a) := by rw [Finset.mul_sum]
    _ = B ^ 2 * (1 + chiSq q p) := by
      rw [chiSq_eq_sum_sq_div p q hq hp1 hq1]
      ring

/-! ## 定理 7（核心）：最优提议分布的下界（Engel 形式 Cauchy–Schwarz）
对任意 q > 0（Σq = 1）：E_q[g²] = Σ_a p_a²f_a²/q_a ≥ (Σ_a p_a|f_a|)²。
证明：`Finset.sq_sum_div_le_sum_sq_div`（Sedrakyan/Titu/Engel）
取 f_a = p_a|f_a|、g_a = q_a：(Σ p|f|)²/Σq ≤ Σ (p|f|)²/q，
再用 Σq = 1 与 (p_a|f_a|)² = p_a²f_a²。 -/

theorem is_optimal_q (p q f : Fin k → ℝ) (hq : ∀ a, 0 < q a) (hq1 : ∑ a, q a = 1) :
    (∑ a, p a * |f a|) ^ 2 ≤ ∑ a, q a * (p a / q a * f a) ^ 2 := by
  have h := Finset.sq_sum_div_le_sum_sq_div (s := Finset.univ)
    (f := fun a => p a * |f a|) (g := q) (fun a _ => hq a)
  rw [hq1, div_one] at h
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro a _
  have hqa : q a ≠ 0 := ne_of_gt (hq a)
  rw [mul_pow, sq_abs]
  field_simp [hqa]
  ring

/-! ## 定理 8：最优提议分布达到下界（q* ∝ p·|f| ⟹ E_{q*}[g²] = (Σp|f|)²） -/

theorem is_optimal_q_attained (p f : Fin k → ℝ) (hk : 0 < k)
    (hpos : ∀ a, 0 < p a * |f a|) :
    (∑ a, isOptimalQ p f a * (p a / isOptimalQ p f a * f a) ^ 2) =
      (∑ a, p a * |f a|) ^ 2 := by
  unfold isOptimalQ
  have hZpos : 0 < ∑ b, p b * |f b| :=
    Finset.sum_pos (fun b _ => hpos b) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hZne : (∑ b, p b * |f b|) ≠ 0 := ne_of_gt hZpos
  calc
    (∑ a, (p a * |f a| / (∑ b, p b * |f b|)) *
        (p a / (p a * |f a| / (∑ b, p b * |f b|)) * f a) ^ 2)
        = ∑ a, (∑ b, p b * |f b|) * (p a * |f a|) := by
          apply Finset.sum_congr rfl
          intro a _
          have h1 : p a * |f a| ≠ 0 := ne_of_gt (hpos a)
          have hpa : p a ≠ 0 := by
            intro h
            rw [h, zero_mul] at h1
            exact h1 rfl
          have hfa : |f a| ≠ 0 := by
            intro h
            rw [h, mul_zero] at h1
            exact h1 rfl
          rw [mul_pow]
          rw [show f a ^ 2 = |f a| ^ 2 from by rw [sq_abs]]
          field_simp [h1, hZne, hpa, hfa]
          rw [show f a ^ 2 = |f a| ^ 2 from by rw [sq_abs]]
          ring
    _ = (∑ b, p b * |f b|) * (∑ a, p a * |f a|) := by rw [Finset.mul_sum]
    _ = (∑ a, p a * |f a|) ^ 2 := by ring

/-! ## 注：与 RealFDivergence / RealSamplingBoost 的衔接
`is_variance_bound` 把重要性采样的方差与 **χ² 散度** 精确挂钩
（方差 ≤ B²(1 + χ²(q‖p))）：提议分布越接近目标（χ² 越小）方差越小；
`is_optimal_q` + `is_optimal_q_attained` 给出下确界 (E_p|f|)² 与达到它的
q* ∝ p·|f|。进一步，重要性采样把「不可采样目标分布 p」上的验证
规约为「可采样提议分布 q」上的验证：无偏性（定理 2）保证期望正确，
方差界（定理 6）与 Berry–Esseen 型 / Markov 型界（RealRandomVerify）
给出样本量需求，再经 RealSamplingBoost 的多轮放大得到置信度 ≥ 1 − ε^k。
诚实标注：本文件未证明「Var_q(g) 的显式下界」（定理 7 给出的是二阶矩
下界，因 Var ≤ E[g²] 已足够导出方差界方向）；KL 形式的下界
（q* 的 KL 最优性）留作后续。 -/

end Lattice
