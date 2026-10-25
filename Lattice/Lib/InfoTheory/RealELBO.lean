import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealCrossEntropy
/-!
# LATTICE: 变分推断 —— ELBO 与证据下界（有限潜变量版）

信息论线的又一块基石（衔接 RealKL 的 KL 非负/零化刻画、RealCrossEntropy 的熵）：

有限潜变量 z ∈ Fin k，联合分布（对固定观测 x 的未归一化联合 p_z = p(x,z)）、
变分分布 q（概率向量）。**证据**为边缘似然 Z = Σ_z p_z。定义

    ELBO(p, q) = Σ_z q_z·(log p_z − log q_z)     （= E_q[log p(x,z) − log q(z)]）

本文件建立变分推断的**核心恒等式与下界**：

  1. `posterior`：后验分布 post_z = p_z / Z；
     `posterior_pos` / `posterior_sum`：p 严格正时 post 是严格正概率向量；
  2. `elbo`：ELBO 的定义；
  3. `elbo_eq_log_marginal_sub_kl`（**核心恒等式**）：
     ELBO(p,q) = log Z − KL(q‖post)；
  4. `elbo_gap_is_kl`：间隙 log Z − ELBO = KL(q‖post)（间隙就是 KL）；
  5. `elbo_le_log_marginal`（**证据下界**）：ELBO(p,q) ≤ log Z
     —— 由 `kl_nonneg`（KL ≥ 0）与第 3 条直接得；
  6. `elbo_tight_iff`（**等号刻画**）：ELBO(p,q) = log Z ⟺ q = post
     —— 由 `kl_zero_iff_eq`（KL = 0 ⟺ 分布相等）闭合；
  7. `em_posterior_optimal`（**EM 单调性 / E 步最优性**）：
     ELBO(p,q) ≤ ELBO(p, post)，且等号 ⟺ q = post
     —— 即「把变分分布取成后验」是最优的 E 步，ELBO 不降；
  8. `elbo_self_kl`: ELBO(p,q) 也可写作 `Σ_z q_z·log p_z + entropy q`
     （衔接 RealCrossEntropy.entropy，暴露 ELBO = 期望对数似然 + 熵）。

**诚实边界**（本文件不证 / 不声称的）：

- 本文件是**有限潜变量**版本：z 取遍有限集 Fin k，p、q 是有限维实向量，
  「期望 E_q」就是有限加权和。连续潜变量版（需要测度积分与 KL 的积分表示）、
  参数化族 q_φ（需要 q 关于 φ 的可导性）标注为后续。
- `p` 不要求归一（它就是 p(x,z)，边缘 Z = Σ p_z 一般 ≠ 1）；只要求严格正
  （log 定义域与后验的正性）。q 要求严格正概率向量（`Σ q = 1`）。
- `em_algorithm_monotone` 的完整形式（参数化 p_θ 与 M 步）未做：本文件证明的是
  **E 步**的最优性与单调性（q 空间上的最大化），M 步需要 p 的参数化与
  似然关于参数的优化，标注为后续。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 定义：后验分布与 ELBO -/

/-- 后验分布：post_z = p_z / Σ_z p_z。 -/
noncomputable def posterior (p : Fin k → ℝ) : Fin k → ℝ :=
  fun z => p z / ∑ z', p z'

/-- 证据下界（ELBO）：ELBO(p,q) = Σ_z q_z·(log p_z − log q_z)。 -/
noncomputable def elbo (p q : Fin k → ℝ) : ℝ :=
  ∑ z, q z * (Real.log (p z) - Real.log (q z))

/-! ## 后验的性质 -/

lemma posterior_pos [Nonempty (Fin k)] (p : Fin k → ℝ) (hp : ∀ z, 0 < p z) :
    ∀ z, 0 < posterior p z := by
  intro z
  unfold posterior
  exact div_pos (hp z) (Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty)

lemma posterior_sum [Nonempty (Fin k)] (p : Fin k → ℝ) (hp : ∀ z, 0 < p z) :
    ∑ z, posterior p z = 1 := by
  have hS : (∑ z, p z) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty)
  unfold posterior
  rw [← Finset.sum_div, div_self hS]

/-! ## 定理一（核心）：ELBO = log Z − KL(q‖post)

证明路线：KL(q‖post) = Σ_z q_z·log(q_z/post_z)（`kl_as_sum_log_ratio`），
逐项 q_z/post_z = q_z·Z/p_z（field_simp），log 展开为 log q_z − log p_z + log Z；
求和后用 Σq = 1 把 log Z 提出来，再与 ELBO 相减即得。 -/

theorem elbo_eq_log_marginal_sub_kl [Nonempty (Fin k)] (p q : Fin k → ℝ)
    (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z) (hqs : ∑ z, q z = 1) :
    elbo p q = Real.log (∑ z, p z) - kl q (posterior p) := by
  have hSpos : 0 < ∑ z, p z := Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty
  have hSne : (∑ z, p z) ≠ 0 := ne_of_gt hSpos
  have hpost_pos : ∀ z, 0 < posterior p z := posterior_pos p hp
  have hpost_sum : ∑ z, posterior p z = 1 := posterior_sum p hp
  -- KL 的显式比值形式
  have hkl := kl_as_sum_log_ratio q (posterior p) hq hpost_pos
  -- log(q_z/post_z) = log q_z − log p_z + log Z
  have hratio : ∀ z, Real.log (q z / posterior p z)
      = Real.log (q z) - Real.log (p z) + Real.log (∑ z, p z) := by
    intro z
    have h1 : q z / posterior p z = (q z * (∑ z, p z)) / p z := by
      unfold posterior
      field_simp [ne_of_gt (hp z), hSne]
    rw [h1, Real.log_div (mul_ne_zero (ne_of_gt (hq z)) hSne) (ne_of_gt (hp z)),
      Real.log_mul (ne_of_gt (hq z)) hSne]
    ring
  -- KL 的求和展开
  have hsum : ∑ z, q z * Real.log (q z / posterior p z)
      = (∑ z, q z * Real.log (q z)) - (∑ z, q z * Real.log (p z))
        + (∑ z, q z) * Real.log (∑ z, p z) := by
    have hterm : ∀ z, q z * Real.log (q z / posterior p z)
        = (q z * Real.log (q z) - q z * Real.log (p z))
          + q z * Real.log (∑ z, p z) := by
      intro z
      rw [hratio z]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_mul]
  have helbo : elbo p q
      = (∑ z, q z * Real.log (p z)) - (∑ z, q z * Real.log (q z)) := by
    unfold elbo
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hkl, hsum, hqs, one_mul, helbo]
  ring

/-! ## 定理二：间隙就是 KL -/

theorem elbo_gap_is_kl [Nonempty (Fin k)] (p q : Fin k → ℝ)
    (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z) (hqs : ∑ z, q z = 1) :
    Real.log (∑ z, p z) - elbo p q = kl q (posterior p) := by
  have h := elbo_eq_log_marginal_sub_kl p q hp hq hqs
  linarith

/-! ## 定理三（核心）：ELBO ≤ log 证据（证据下界） -/

theorem elbo_le_log_marginal [Nonempty (Fin k)] (p q : Fin k → ℝ)
    (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z) (hqs : ∑ z, q z = 1) :
    elbo p q ≤ Real.log (∑ z, p z) := by
  have hpost_pos : ∀ z, 0 < posterior p z := posterior_pos p hp
  have hpost_sum : ∑ z, posterior p z = 1 := posterior_sum p hp
  have hkl : 0 ≤ kl q (posterior p) :=
    kl_nonneg q (posterior p) hq hqs hpost_pos hpost_sum
  have heq := elbo_eq_log_marginal_sub_kl p q hp hq hqs
  linarith

/-! ## 定理四（核心）：等号刻画 —— ELBO 紧 ⟺ q 就是后验 -/

theorem elbo_tight_iff [Nonempty (Fin k)] (p q : Fin k → ℝ)
    (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z) (hqs : ∑ z, q z = 1) :
    elbo p q = Real.log (∑ z, p z) ↔ q = posterior p := by
  have hpost_pos : ∀ z, 0 < posterior p z := posterior_pos p hp
  have hpost_sum : ∑ z, posterior p z = 1 := posterior_sum p hp
  have hz := kl_zero_iff_eq q (posterior p) hq hqs hpost_pos hpost_sum
  have hpost_eq : elbo p (posterior p) = Real.log (∑ z, p z) := by
    rw [elbo_eq_log_marginal_sub_kl p (posterior p) hp hpost_pos hpost_sum,
      kl_eq_zero_of_eq (posterior p) (posterior p) rfl]
    ring
  constructor
  · intro h
    apply hz.mp
    linarith [elbo_eq_log_marginal_sub_kl p q hp hq hqs]
  · intro h
    rw [h, hpost_eq]

/-! ## 定理五（核心）：EM 的 E 步最优性（ELBO 不降）

把变分分布取成后验 post 使 ELBO 达到证据上界 log Z（ELBO 的最大值），
且它是唯一的最优点（等号 ⟺ q = post）。这就是 EM 单调性的 E 步半边。 -/

theorem em_posterior_optimal [Nonempty (Fin k)] (p q : Fin k → ℝ)
    (hp : ∀ z, 0 < p z) (hq : ∀ z, 0 < q z) (hqs : ∑ z, q z = 1) :
    elbo p q ≤ elbo p (posterior p) ∧ (elbo p q = elbo p (posterior p) ↔ q = posterior p) := by
  have hpost_pos : ∀ z, 0 < posterior p z := posterior_pos p hp
  have hpost_sum : ∑ z, posterior p z = 1 := posterior_sum p hp
  have h1 : elbo p q ≤ Real.log (∑ z, p z) := elbo_le_log_marginal p q hp hq hqs
  have h2 : elbo p (posterior p) = Real.log (∑ z, p z) := by
    rw [elbo_eq_log_marginal_sub_kl p (posterior p) hp hpost_pos hpost_sum,
      kl_eq_zero_of_eq (posterior p) (posterior p) rfl]
    ring
  constructor
  · rw [h2]; exact h1
  · rw [h2]
    exact elbo_tight_iff p q hp hq hqs

/-! ## 定理六：ELBO = 期望对数似然 + 熵（衔接 RealCrossEntropy.entropy） -/

theorem elbo_eq_sum_log_p_add_entropy (p q : Fin k → ℝ) :
    elbo p q = (∑ z, q z * Real.log (p z)) + entropy q := by
  have h1 : entropy q = -∑ z, q z * Real.log (q z) := rfl
  have h2 : ∑ z, q z * Real.log (q z) = -entropy q := by
    rw [h1]; ring
  have h3 : elbo p q
      = (∑ z, q z * Real.log (p z)) - (∑ z, q z * Real.log (q z)) := by
    unfold elbo
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [h3, h2]
  ring

end Lattice
