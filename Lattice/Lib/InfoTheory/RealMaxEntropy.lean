import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealCrossEntropy
/-!
# LATTICE: 最大熵原理 —— 均匀分布最大化熵、等号刻画与矩约束下的指数族

信息论线的收官一环（衔接 RealCrossEntropy 的 CE/熵、RealKL 的 KL 与零化刻画）：

**最大熵原理**：在所有支撑于有限集 Fin k（k > 0）的概率向量中，均匀分布
u_a = 1/k 唯一地最大化熵 H(p) = −Σ_a p_a·log p_a。

证明路线（最稳，全部复用既有设施）：
  KL(p‖u) = CE(p,u) − H(p) = log k − H(p)（CE(p,u) = log k，由 `crossEntropy_unif`），
  再套 Gibbs 非负 `kl_nonneg` 得 H(p) ≤ log k；等号由 `kl_zero_iff_eq`（KL = 0 ⟺ p = u）闭合。

本文件建立：

  1. `unifDist` / `unifDist_pos` / `unifDist_sum`：均匀分布及其概率向量性质；
  2. `crossEntropy_unif`：CE(p, u) = log k（p 为概率向量、k ≠ 0）；
  3. `entropy_le_log_card`（核心）：H(p) ≤ log k（= log (Fintype.card (Fin k))；
     p 严格正概率向量），即任何分布的熵不超过 log 支撑大小；
  4. `entropy_unif`：H(u) = log k；
  5. `entropy_maximized_by_uniform`（核心）：H(p) ≤ H(u)（均匀分布最大化熵）；
  6. `entropy_eq_log_card_iff_uniform`（核心）：H(p) = log k ⟺ p = u
     （等号刻画：熵最大当且仅当分布是均匀分布）；
  7. `gibbsPartition` / `gibbsDist` / `crossEntropy_gibbs` / `maxEntropy_with_moment_constraint`
     （加分）：矩约束下的最大熵——指数族（Gibbs 分布）q_a ∝ exp(θ·g_a)
     在与待比较分布 p 共享同一矩 Σ p_a·g_a 时熵不小于 p
     （证明：CE(p,q) = −θ·Σp·g + log Z 只依赖矩，故 CE(p,q) = H(q)，再由 Gibbs H(p) ≤ CE(p,q)）。

**诚实边界**（本文件不证 / 不声称的）：

- 所有陈述在**严格正**概率向量上（mathlib 的 `Real.log` 在非正处取 0 全函数，
  含零支撑时熵的约定会退化；含零情形标注为后续）。
- `maxEntropy_with_moment_constraint` 把「矩约束」表述为**待比较分布 p 与指数族 q
  共享同一矩**（即 KKT 一阶条件 / 拉格朗日乘子已经解出后的形式），
  **不**断言矩约束确定唯一 θ（那需要配分函数 log Z 的严格凸性与单调性）。
  这是诚实的降级：本文件证的是「指数族在给定矩下最大化熵」的变分刻画，
  而非「给定矩存在唯一指数族」。
- 未做：连续分布的最大熵、最大熵与指数族的充分统计量 / 凸共轭对偶。

模型无关：任意有限 k。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 定义：均匀分布 -/

/-- 有限集 Fin k 上的均匀分布：u_a = 1/k。 -/
noncomputable def unifDist (k : ℕ) : Fin k → ℝ := fun _ => (k : ℝ)⁻¹

/-- 均匀分布严格正（k ≠ 0）。 -/
lemma unifDist_pos (hk : k ≠ 0) (a : Fin k) : 0 < unifDist k a := by
  unfold unifDist
  exact inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hk)

/-- 均匀分布是概率向量（k ≠ 0）。 -/
lemma unifDist_sum (hk : k ≠ 0) : ∑ a : Fin k, unifDist k a = 1 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have h : ∑ a : Fin k, unifDist k a = ∑ _a : Fin k, (k : ℝ)⁻¹ :=
    Finset.sum_congr rfl (fun a _ => rfl)
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (ne_of_gt hkpos)

/-! ## 定理一：CE(p, u) = log k

crossEntropy p u = −Σ_a p_a·log((k)⁻¹) = −log(k⁻¹)·Σ_a p_a = log k（Σp = 1、k ≠ 0）。 -/

lemma crossEntropy_unif (p : Fin k → ℝ) (hpsum : ∑ a, p a = 1) :
    crossEntropy p (unifDist k) = Real.log k := by
  have hterm : ∀ a : Fin k, p a * Real.log (unifDist k a) = p a * (-Real.log k) := by
    intro a
    unfold unifDist
    rw [Real.log_inv]
  unfold crossEntropy
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [← Finset.sum_mul, hpsum]
  ring

/-! ## 定理二（核心）：熵的上界 H(p) ≤ log k

KL(p‖u) = CE(p,u) − H(p) = log k − H(p) ≥ 0（`kl_nonneg`）⟹ H(p) ≤ log k。
k = Fintype.card (Fin k)（`Fintype.card_fin`），故这是「熵 ≤ log 支撑大小」。 -/

theorem entropy_le_log_card (p : Fin k → ℝ) (hp0 : ∀ a, 0 < p a)
    (hpsum : ∑ a, p a = 1) :
    entropy p ≤ Real.log k := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hpsum
  have hkl := kl_nonneg p (unifDist k) hp0 hpsum (unifDist_pos hk) (unifDist_sum hk)
  have hce := crossEntropy_unif p hpsum
  have hbridge : kl p (unifDist k) = Real.log k - entropy p := by
    unfold kl
    rw [hce]
  linarith

/-! ## 定理三：均匀分布的熵恰为 log k -/

theorem entropy_unif (hk : k ≠ 0) : entropy (unifDist k) = Real.log k := by
  have hce := crossEntropy_unif (unifDist k) (unifDist_sum hk)
  unfold entropy
  exact hce

/-! ## 定理四（核心）：均匀分布最大化熵

任意严格正概率向量 p 的熵不超过均匀分布的熵 H(u) = log k。 -/

theorem entropy_maximized_by_uniform (p : Fin k → ℝ) (hp0 : ∀ a, 0 < p a)
    (hpsum : ∑ a, p a = 1) :
    entropy p ≤ entropy (unifDist k) := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hpsum
  rw [entropy_unif hk]
  exact entropy_le_log_card p hp0 hpsum

/-! ## 定理五（核心）：等号刻画 —— 熵最大 ⟺ 均匀分布

H(p) = log k ⟺ p = u。证明：H(p) = log k ⟺ KL(p‖u) = 0（桥 KL = log k − H），
再由 `kl_zero_iff_eq`（KL = 0 ⟺ p = u）闭合。 -/

theorem entropy_eq_log_card_iff_uniform (p : Fin k → ℝ) (hp0 : ∀ a, 0 < p a)
    (hpsum : ∑ a, p a = 1) :
    entropy p = Real.log k ↔ p = unifDist k := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hpsum
  have hce := crossEntropy_unif p hpsum
  have hbridge : kl p (unifDist k) = Real.log k - entropy p := by
    unfold kl
    rw [hce]
  have hz := kl_zero_iff_eq p (unifDist k) hp0 hpsum (unifDist_pos hk) (unifDist_sum hk)
  constructor
  · intro h
    apply hz.mp
    rw [hbridge, h]
    ring
  · intro h
    rw [h]
    exact entropy_unif hk

/-! ## 加分：矩约束下的最大熵（指数族 / Gibbs 分布）

配分函数 Z(θ) = Σ_a exp(θ·g_a)、Gibbs 分布 q_a = exp(θ·g_a)/Z(θ)。
核心恒等式 `crossEntropy_gibbs`：CE(r, q) = −θ·(Σ_a r_a·g_a) + log Z(θ)，
即 CE 只通过「矩」Σ r_a·g_a 依赖 r。于是若 p 与 q 共享同一矩，
则 CE(p,q) = H(q)，配合 Gibbs 不等式 H(p) ≤ CE(p,q) 得 H(p) ≤ H(q)。 -/

/-- 配分函数 Z(θ) = Σ_a exp(θ·g_a)。 -/
noncomputable def gibbsPartition (g : Fin k → ℝ) (theta : ℝ) : ℝ :=
  ∑ a, Real.exp (theta * g a)

/-- 指数族（Gibbs 分布）：q_a = exp(θ·g_a)/Z(θ)。 -/
noncomputable def gibbsDist (g : Fin k → ℝ) (theta : ℝ) : Fin k → ℝ :=
  fun a => Real.exp (theta * g a) / gibbsPartition g theta

/-- 配分函数严格正（非空指标集）。 -/
lemma gibbsPartition_pos [Nonempty (Fin k)] (g : Fin k → ℝ) (theta : ℝ) :
    0 < gibbsPartition g theta :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Gibbs 分布分量严格正。 -/
lemma gibbsDist_pos [Nonempty (Fin k)] (g : Fin k → ℝ) (theta : ℝ) :
    ∀ a, 0 < gibbsDist g theta a := by
  intro a
  unfold gibbsDist
  exact div_pos (Real.exp_pos _) (gibbsPartition_pos g theta)

/-- Gibbs 分布是概率向量。 -/
lemma gibbsDist_sum [Nonempty (Fin k)] (g : Fin k → ℝ) (theta : ℝ) :
    ∑ a, gibbsDist g theta a = 1 := by
  have hZ : (∑ a, Real.exp (theta * g a)) ≠ 0 := ne_of_gt (gibbsPartition_pos g theta)
  simp only [gibbsDist, gibbsPartition]
  rw [← Finset.sum_div, div_self hZ]

/-- 核心恒等式：CE(r, q) = −θ·(Σ_a r_a·g_a) + log Z(θ)（r 为概率向量）。
右侧只通过矩 Σ r_a·g_a 依赖 r，这是「指数族是矩约束下的最大熵分布」的代数核心。 -/
lemma crossEntropy_gibbs [Nonempty (Fin k)] (g r : Fin k → ℝ) (theta : ℝ)
    (hsum : ∑ a, r a = 1) :
    crossEntropy r (gibbsDist g theta)
      = -theta * (∑ a, r a * g a) + Real.log (gibbsPartition g theta) := by
  have hlog : ∀ a, Real.log (gibbsDist g theta a)
      = theta * g a - Real.log (gibbsPartition g theta) := by
    intro a
    unfold gibbsDist
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (gibbsPartition_pos g theta)),
      Real.log_exp]
  have hs : ∑ a, r a * (theta * g a - Real.log (gibbsPartition g theta))
      = theta * (∑ a, r a * g a)
        - (∑ a, r a) * Real.log (gibbsPartition g theta) := by
    have hterm : ∀ a : Fin k,
        r a * (theta * g a - Real.log (gibbsPartition g theta))
          = theta * (r a * g a) - r a * Real.log (gibbsPartition g theta) := by
      intro a
      ring
    calc ∑ a, r a * (theta * g a - Real.log (gibbsPartition g theta))
        = ∑ a, (theta * (r a * g a) - r a * Real.log (gibbsPartition g theta)) :=
          Finset.sum_congr rfl (fun a _ => hterm a)
      _ = (∑ a, theta * (r a * g a)) - ∑ a, r a * Real.log (gibbsPartition g theta) :=
          Finset.sum_sub_distrib
      _ = theta * (∑ a, r a * g a)
            - (∑ a, r a) * Real.log (gibbsPartition g theta) := by
          rw [Finset.mul_sum, Finset.sum_mul]
  unfold crossEntropy
  rw [Finset.sum_congr rfl (fun a _ => by rw [hlog a]), hs, hsum]
  ring

/-- 矩约束下的最大熵（指数族变分刻画）：
若 p（严格正概率向量）与指数族 q = Gibbs(g, θ) 共享同一矩 Σ p_a·g_a，
则 H(p) ≤ H(q)。证明：Gibbs 不等式 H(p) ≤ CE(p,q)，
而 `crossEntropy_gibbs` 给出 CE(p,q) = −θ·矩 + log Z = H(q)。 -/
theorem maxEntropy_with_moment_constraint (g p : Fin k → ℝ) (theta : ℝ)
    (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hmoment : ∑ a, p a * g a = ∑ a, gibbsDist g theta a * g a) :
    entropy p ≤ entropy (gibbsDist g theta) := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hpsum
  haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hq0 : ∀ a, 0 < gibbsDist g theta a := gibbsDist_pos g theta
  have hqs : ∑ a, gibbsDist g theta a = 1 := gibbsDist_sum g theta
  have hge := ce_ge_entropy p (gibbsDist g theta) hp0 hpsum hq0 hqs
  have hce := crossEntropy_gibbs g p theta hpsum
  have hqe : entropy (gibbsDist g theta)
      = -theta * (∑ a, p a * g a) + Real.log (gibbsPartition g theta) := by
    unfold entropy
    rw [crossEntropy_gibbs g (gibbsDist g theta) theta hqs, ← hmoment]
  rw [hce] at hge
  rw [← hqe] at hge
  exact hge

end Lattice
