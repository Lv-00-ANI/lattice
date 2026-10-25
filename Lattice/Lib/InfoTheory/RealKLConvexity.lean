import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.Convex.RealConvexToolkit
/-!
# LATTICE: KL 的凸性 —— 对数凹性引理、CE 对 q 凸、KL 对 q 与对 p 凸

信息论线的推广（衔接 RealKL 的 KL 非负/零化刻画）：

KL 的标准性质是**联合凸**。本文件用**初等方法**（只用 `log x ≤ x − 1`，
避免依赖 mathlib 中凸性引理的确切命名）建立两条单侧凸性：

  1. `log_concave_two`（核心工具）：log 的两点凹性
     λ·log x + (1−λ)·log y ≤ log(λ·x + (1−λ)·y)（x, y > 0、λ ∈ [0,1]）；
  2. `ce_convex_in_q`：交叉熵对第二个参数 **凸**：
     CE(p, λq₁+(1−λ)q₂) ≤ λ·CE(p,q₁) + (1−λ)·CE(p,q₂)（p ≥ 0、q > 0）；
  3. `kl_convex_in_q`：KL 对第二个参数凸（H(p) 与 q 无关，直接由 2 得）；
  4. `mul_log_convex_two`（核心工具）：t·log(t/q) 的两点凸性
     m·log(m/q) ≤ λ·x·log(x/q) + (1−λ)·y·log(y/q)，m = λx + (1−λ)y；
  5. `kl_convex_in_p`：KL 对第一个参数凸（逐项用 4）。

证明要点（两点凹/凸性的初等证法）：
  设 m = λx + (1−λ)y > 0。对凹性，把差写成
    λ·log x + (1−λ)·log y − log m = λ·log(x/m) + (1−λ)·log(y/m)
  再用 `Real.log_le_sub_one_of_pos`：log(x/m) ≤ x/m − 1、log(y/m) ≤ y/m − 1，
  加权求和 = (λx + (1−λ)y)/m − 1 = 0。凸性同法（符号相反）。

诚实边界：只证**单侧凸性**（分别对 p、对 q）；**联合凸**（(p,q) 双变量的凸性，
即 log-sum 不等式的完整形式）标注为后续，未在此声称。所有 log 等式在正性假设下陈述。

模型无关：任意有限 k。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 混合分布：m_a = λ·q₁_a + (1−λ)·q₂_a -/

/-- 两个分布的凸混合（逐分量）。 -/
noncomputable def mixDist (lam : ℝ) (q1 q2 : Fin k → ℝ) : Fin k → ℝ :=
  fun a => lam * q1 a + (1 - lam) * q2 a

/-- 混合保严格正（q₁, q₂ > 0、λ ∈ [0,1]）。 -/
lemma mixDist_pos (q1 q2 : Fin k → ℝ) (h1 : ∀ a, 0 < q1 a) (h2 : ∀ a, 0 < q2 a)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (a : Fin k) : 0 < mixDist lam q1 q2 a := by
  unfold mixDist
  rcases eq_or_lt_of_le hlam0 with h0 | h0
  · rw [← h0]
    rw [zero_mul, zero_add, sub_zero, one_mul]
    exact h2 a
  · have hmul : 0 < lam * q1 a := mul_pos h0 (h1 a)
    have hle : 0 ≤ (1 - lam) * q2 a := mul_nonneg (by linarith) (le_of_lt (h2 a))
    linarith

/-! ## 工具引理：log 的两点凹性（初等，仅用 log x ≤ x − 1） -/

-- 迁移到权威位置（REFACTOR.md Step 2）：原初等证明见 RealConvexToolkit.log_concave_pair
lemma log_concave_two {x y lam : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * Real.log x + (1 - lam) * Real.log y ≤ Real.log (lam * x + (1 - lam) * y) :=
  log_concave_pair hx hy hlam0 hlam1

/-! ## 定理一：交叉熵对第二个参数凸
CE(p, λq₁+(1−λ)q₂) ≤ λ·CE(p,q₁) + (1−λ)·CE(p,q₂)（p ≥ 0、q > 0）。 -/

theorem ce_convex_in_q (p q1 q2 : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hq1 : ∀ a, 0 < q1 a) (hq2 : ∀ a, 0 < q2 a) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    crossEntropy p (mixDist lam q1 q2)
      ≤ lam * crossEntropy p q1 + (1 - lam) * crossEntropy p q2 := by
  rw [ce_sum_neg p (mixDist lam q1 q2), ce_sum_neg p q1, ce_sum_neg p q2]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hmix : 0 < mixDist lam q1 q2 a := mixDist_pos q1 q2 hq1 hq2 hlam0 hlam1 a
  have hlog : Real.log (mixDist lam q1 q2 a) ≥ lam * Real.log (q1 a) + (1 - lam) * Real.log (q2 a) :=
    log_concave_two (hq1 a) (hq2 a) hlam0 hlam1
  have hneg : -Real.log (mixDist lam q1 q2 a)
      ≤ lam * (-Real.log (q1 a)) + (1 - lam) * (-Real.log (q2 a)) := by linarith
  calc
    p a * (-Real.log (mixDist lam q1 q2 a))
        ≤ p a * (lam * (-Real.log (q1 a)) + (1 - lam) * (-Real.log (q2 a))) :=
          mul_le_mul_of_nonneg_left hneg (hp0 a)
    _ = lam * (p a * (-Real.log (q1 a))) + (1 - lam) * (p a * (-Real.log (q2 a))) := by ring

/-! ## 定理二：KL 对第二个参数凸
KL(p, λq₁+(1−λ)q₂) ≤ λ·KL(p,q₁) + (1−λ)·KL(p,q₂)（H(p) 与 q 无关）。 -/

theorem kl_convex_in_q (p q1 q2 : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hq1 : ∀ a, 0 < q1 a) (hq2 : ∀ a, 0 < q2 a) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    kl p (mixDist lam q1 q2) ≤ lam * kl p q1 + (1 - lam) * kl p q2 := by
  have h := ce_convex_in_q p q1 q2 hp0 hq1 hq2 hlam0 hlam1
  have hsum1 : lam + (1 - lam) = 1 := by ring
  unfold kl
  linarith [h, hsum1]

/-! ## 工具引理：t·log(t/q) 的两点凸性（初等）
m = λx + (1−λ)y ⟹ m·log(m/q) ≤ λ·x·log(x/q) + (1−λ)·y·log(y/q)（x, y, q > 0）。 -/

-- 迁移到权威位置（REFACTOR.md Step 2）：原初等证明见 RealConvexToolkit.mul_log_convex_pair
lemma mul_log_convex_two {x y q lam : ℝ} (hx : 0 < x) (hy : 0 < y) (hq : 0 < q)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (lam * x + (1 - lam) * y) * Real.log ((lam * x + (1 - lam) * y) / q)
      ≤ lam * (x * Real.log (x / q)) + (1 - lam) * (y * Real.log (y / q)) :=
  mul_log_convex_pair hx hy hq hlam0 hlam1

/-! ## 定理三：KL 对第一个参数凸
KL(λp₁+(1−λ)p₂ ‖ q) ≤ λ·KL(p₁‖q) + (1−λ)·KL(p₂‖q)（p₁, p₂, q 严格正）。

诚实标注：为保持证明干净，此处陈述在 **p₁、p₂ 严格正**下（log 定义域）；
p 仅非负的边界情形（p_a = 0 时该坐标为 0·log 0 = 0）未展开，标注为后续。 -/

theorem kl_convex_in_p (p1 p2 q : Fin k → ℝ) (hp1 : ∀ a, 0 < p1 a) (hp2 : ∀ a, 0 < p2 a)
    (hq : ∀ a, 0 < q a) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    kl (mixDist lam p1 p2) q ≤ lam * kl p1 q + (1 - lam) * kl p2 q := by
  rw [kl_as_sum_log_sub_log (mixDist lam p1 p2) q, kl_as_sum_log_sub_log p1 q,
    kl_as_sum_log_sub_log p2 q]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have h1 := mul_log_convex_two (hp1 a) (hp2 a) (hq a) hlam0 hlam1
  have hmixpos : 0 < lam * p1 a + (1 - lam) * p2 a :=
    mixDist_pos p1 p2 hp1 hp2 hlam0 hlam1 a
  rw [Real.log_div (ne_of_gt (hp1 a)) (ne_of_gt (hq a)),
      Real.log_div (ne_of_gt (hp2 a)) (ne_of_gt (hq a)),
      Real.log_div (ne_of_gt hmixpos) (ne_of_gt (hq a))] at h1
  simpa only [mixDist] using h1

end Lattice
