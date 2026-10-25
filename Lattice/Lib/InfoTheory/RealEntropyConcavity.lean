import Mathlib
import Lattice.Lib.InfoTheory.RealKL
/-!
# LATTICE: 熵的凹性（concavity of entropy）—— 混合熵恒等式与 KL 衔接

RealCrossEntropy 定义熵 `entropy`（H(p) = −Σ p·log p）与交叉熵 `crossEntropy`；
RealKL 在其上定义 KL 散度 `kl`（KL(p‖q) = CE(p,q) − H(p)）并证明 `kl_nonneg`（Gibbs：KL ≥ 0）。
本文件在此之上证明**熵的凹性**：混合分布 r = lam·p + (1−lam)·q 的熵不小于
分量熵的加权平均 H(r) ≥ lam·H(p) + (1−lam)·H(q)（信息论核心性质，
衔接 RealKL/RealCrossEntropy 的信息量线）。

**证明路线（信息论恒等式，只用 Finset 求和 + log_mul/log_div 的线性展开，最稳）**：

  1. `mix`：混合分布 r_a = lam·p_a + (1−lam)·q_a（凸组合）；
  2. `mix_is_pmf`：r 是概率向量（0 ≤ r、Σr = 1 —— Finset 线性）；
  3. `entropy_mix_identity`（混合熵恒等式，核心）：
     H(r) = lam·H(p) + (1−lam)·H(q) + lam·KL(p‖r) + (1−lam)·KL(q‖r)
     —— 纯 Finset 求和展开（`sum_add_distrib`/`mul_sum`/`sum_neg_distrib`/逐项 ring），
     不依赖任何 log 不等式，`Real.log` 为全函数故无需假设；
  4. `entropy_concave`（核心定理）：恒等式 + `kl_nonneg`（KL ≥ 0）⟹
     H(r) ≥ lam·H(p) + (1−lam)·H(q)（KL 非负的直接推论）；
  5. 加分：
     - `kl_pos_of_ne`：p ≠ q（均严格正概率向量）⟹ KL(p‖q) > 0
       （由 `kl_nonneg` + `kl_zero_iff_eq` 闭合：KL = 0 ⟺ p = q）；
     - `entropy_concavity_strict`：p ≠ q、lam ∈ (0,1) ⟹ 严格不等
       H(r) > lam·H(p) + (1−lam)·H(q)；
     - `entropy_concavity_eq_iff`：H(r) = lam·H(p) + (1−lam)·H(q)
       ⟺ lam ∈ {0,1} ∨ p = q（0 < lam < 1 时两项 KL 各自为零 ⟹ p = r = q）。

**诚实边界**（本文件不证 / 不声称的）：
- `entropy_mix_identity` 是纯代数恒等式，无任何假设
  （mathlib 的 `Real.log` 是非正处取 0 的全函数，恒等式在含零分布下仍成立）；
- KL 非负（`kl_nonneg`）需要 log 定义域假设：0 < p a、0 < q a、0 < r a。
  `mix_pos` 证明：lam ∈ [0,1] 且 p、q 严格正 ⟹ r = lam·p + (1−lam)·q 严格正
  （lam = 0 时 r = q；lam > 0 时 lam·p_a > 0 加非负项）；
- 凹性只对**严格正**概率向量陈述（含零的分布熵会退化）；
- 等式刻画的正向方向需要 0 < lam < 1（否则退化情形 lam ∈ {0,1} 平凡成立）。
- 未做：log 的凸性路线（`Real.convexOn_mul_log` 逐点凸性）与 Jensen 形式；
  本文件采用 KL 恒等式路线，证明最稳。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 定义：混合分布 -/

/-- 混合分布：r_a = lam·p_a + (1−lam)·q_a（p、q 的凸组合）。-/
def mix {k : ℕ} (lam : ℝ) (p q : Fin k → ℝ) : Fin k → ℝ :=
  fun a => lam * p a + (1 - lam) * q a

/-! ## 定理一：混合是概率向量
r = lam·p + (1−lam)·q 满足 0 ≤ r（两项均非负）且 Σr = 1（Finset 线性 + Σp = Σq = 1）。-/

theorem mix_is_pmf {k : ℕ} (lam : ℝ) (p q : Fin k → ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hp0 : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1) :
    (∀ a, 0 ≤ mix lam p q a) ∧ ∑ a, mix lam p q a = 1 := by
  constructor
  · intro a
    unfold mix
    exact add_nonneg (mul_nonneg hlam0 (hp0 a)) (mul_nonneg (sub_nonneg.mpr hlam1) (hq0 a))
  · unfold mix
    calc
      (∑ a, (lam * p a + (1 - lam) * q a))
          = (∑ a, lam * p a) + ∑ a, (1 - lam) * q a := by
            rw [Finset.sum_add_distrib]
      _ = lam * (∑ a, p a) + (1 - lam) * (∑ a, q a) := by
            rw [Finset.mul_sum, Finset.mul_sum]
      _ = lam * 1 + (1 - lam) * 1 := by rw [hpsum, hqsum]
      _ = 1 := by ring

/-! ## 引理：混合的严格正性（log 定义域前提）
lam ∈ [0,1] 且 p、q 严格正 ⟹ r = lam·p + (1−lam)·q 严格正。
lam = 0 时 r = q；lam > 0 时 lam·p_a > 0 加上非负项。-/

lemma mix_pos {k : ℕ} (lam : ℝ) (p q : Fin k → ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hp0 : ∀ a, 0 < p a) (hq0 : ∀ a, 0 < q a) : ∀ a, 0 < mix lam p q a := by
  intro a
  unfold mix
  rcases eq_or_lt_of_le hlam0 with hlamz | hlamgt
  · -- lam = 0：r = q
    subst lam
    simpa using (hq0 a)
  · -- lam > 0：lam·p a > 0，加非负项
    have h1 : 0 < lam * p a := mul_pos hlamgt (hp0 a)
    have h2 : 0 ≤ (1 - lam) * q a := mul_nonneg (sub_nonneg.mpr hlam1) (le_of_lt (hq0 a))
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_right h2)

/-! ## 引理：严格正概率向量的混合仍是严格正概率向量
（`mix_pos` + `mix_is_pmf` 的合取，供 `kl_nonneg`/`kl_zero_iff_eq` 复用。）-/

lemma mix_pmf_strict {k : ℕ} (lam : ℝ) (p q : Fin k → ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) :
    (∀ a, 0 < mix lam p q a) ∧ ∑ a, mix lam p q a = 1 := by
  constructor
  · exact mix_pos lam p q hlam0 hlam1 hp0 hq0
  · exact (mix_is_pmf lam p q hlam0 hlam1 (fun a => le_of_lt (hp0 a)) hpsum
      (fun a => le_of_lt (hq0 a)) hqsum).2

/-! ## 定理二：混合熵恒等式（核心）
H(r) = lam·H(p) + (1−lam)·H(q) + lam·KL(p‖r) + (1−lam)·KL(q‖r)，r = mix lam p q。
证明：先化简 KL 项——lam·H(p) + lam·KL(p‖r) = lam·CE(p,r)（H 与 KL 的 CE 项抵消），
再证 H(r) = lam·CE(p,r) + (1−lam)·CE(q,r)：
H(r) = −Σ r·log r = −Σ (lam·p + (1−lam)·q)·log r
     = −lam·Σ p·log r − (1−lam)·Σ q·log r
     = lam·CE(p,r) + (1−lam)·CE(q,r)。
纯 Finset 线性（`sum_add_distrib`/`mul_sum`/`sum_neg_distrib`），无需任何假设。 -/

theorem entropy_mix_identity {k : ℕ} (p q : Fin k → ℝ) (lam : ℝ) :
    entropy (mix lam p q)
      = lam * entropy p + (1 - lam) * entropy q
          + lam * kl p (mix lam p q) + (1 - lam) * kl q (mix lam p q) := by
  let r : Fin k → ℝ := mix lam p q
  -- RHS 化简：lam·H(p) + (1−lam)·H(q) + lam·KL(p‖r) + (1−lam)·KL(q‖r) = lam·CE(p,r) + (1−lam)·CE(q,r)
  have hsimple : lam * entropy p + (1 - lam) * entropy q + lam * kl p r + (1 - lam) * kl q r
      = lam * crossEntropy p r + (1 - lam) * crossEntropy q r := by
    unfold kl
    ring
  -- H(r) = lam·CE(p,r) + (1−lam)·CE(q,r)
  have hmain : entropy r = lam * crossEntropy p r + (1 - lam) * crossEntropy q r := by
    -- r a = lam·p a + (1−lam)·q a
    have hra : ∀ a, r a = lam * p a + (1 - lam) * q a := by
      intro a
      rfl
    -- Σ r·log r = lam·Σ p·log r + (1−lam)·Σ q·log r（逐项线性 + Finset 线性）
    have hsum : (∑ a, r a * Real.log (r a))
        = lam * (∑ a, p a * Real.log (r a))
            + (1 - lam) * (∑ a, q a * Real.log (r a)) := by
      calc
        (∑ a, r a * Real.log (r a))
            = ∑ a, (lam * p a + (1 - lam) * q a) * Real.log (r a) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [hra a]
        _ = ∑ a, (lam * (p a * Real.log (r a))
              + (1 - lam) * (q a * Real.log (r a))) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = (∑ a, lam * (p a * Real.log (r a)))
            + ∑ a, (1 - lam) * (q a * Real.log (r a)) := by
              rw [Finset.sum_add_distrib]
        _ = lam * (∑ a, p a * Real.log (r a))
            + (1 - lam) * (∑ a, q a * Real.log (r a)) := by
              rw [Finset.mul_sum, Finset.mul_sum]
    -- lam·Σ p·(−log r) = −(lam·Σ p·log r)（q 同理）
    have hneg1 : lam * (∑ a, p a * (-Real.log (r a)))
        = -(lam * (∑ a, p a * Real.log (r a))) := by
      calc
        lam * (∑ a, p a * (-Real.log (r a)))
            = ∑ a, lam * (p a * (-Real.log (r a))) := by rw [Finset.mul_sum]
        _ = ∑ a, -(lam * (p a * Real.log (r a))) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = -(∑ a, lam * (p a * Real.log (r a))) := by rw [Finset.sum_neg_distrib]
        _ = -(lam * (∑ a, p a * Real.log (r a))) := by rw [Finset.mul_sum]
    have hneg2 : (1 - lam) * (∑ a, q a * (-Real.log (r a)))
        = -((1 - lam) * (∑ a, q a * Real.log (r a))) := by
      calc
        (1 - lam) * (∑ a, q a * (-Real.log (r a)))
            = ∑ a, (1 - lam) * (q a * (-Real.log (r a))) := by rw [Finset.mul_sum]
        _ = ∑ a, -((1 - lam) * (q a * Real.log (r a))) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = -(∑ a, (1 - lam) * (q a * Real.log (r a))) := by rw [Finset.sum_neg_distrib]
        _ = -((1 - lam) * (∑ a, q a * Real.log (r a))) := by rw [Finset.mul_sum]
    -- H(r) = −Σ r·log r = lam·CE(p,r) + (1−lam)·CE(q,r)
    unfold entropy
    rw [ce_sum_neg r r, ce_sum_neg p r, ce_sum_neg q r]
    calc
      (∑ a, r a * (-Real.log (r a)))
          = -∑ a, r a * Real.log (r a) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = -(lam * (∑ a, p a * Real.log (r a))
            + (1 - lam) * (∑ a, q a * Real.log (r a))) := by
            rw [hsum]
      _ = lam * (∑ a, p a * (-Real.log (r a)))
          + (1 - lam) * (∑ a, q a * (-Real.log (r a))) := by
            rw [hneg1, hneg2]
            ring
  -- 合成
  calc
    entropy (mix lam p q) = entropy r := rfl
    _ = lam * crossEntropy p r + (1 - lam) * crossEntropy q r := hmain
    _ = lam * entropy p + (1 - lam) * entropy q + lam * kl p r + (1 - lam) * kl q r := hsimple.symm

/-! ## 定理三：熵的凹性（核心）
H(lam·p + (1−lam)·q) ≥ lam·H(p) + (1−lam)·H(q)（lam ∈ [0,1]，p、q 严格正概率向量）。
证明：混合熵恒等式 ⟹ H(r) − [lam·H(p) + (1−lam)·H(q)] = lam·KL(p‖r) + (1−lam)·KL(q‖r)，
RHS 是两项非负 KL 的非负加权和（`kl_nonneg`），故非负。-/

theorem entropy_concave {k : ℕ} (p q : Fin k → ℝ) (lam : ℝ)
    (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * entropy p + (1 - lam) * entropy q ≤ entropy (mix lam p q) := by
  let r : Fin k → ℝ := mix lam p q
  have hpmf : (∀ a, 0 < mix lam p q a) ∧ ∑ a, mix lam p q a = 1 :=
    mix_pmf_strict lam p q hlam0 hlam1 hp0 hpsum hq0 hqsum
  have hr0 : ∀ a, 0 < r a := by
    intro a
    exact (hpmf.1) a
  have hrs : ∑ a, r a = 1 := hpmf.2
  have hklp : 0 ≤ kl p r := kl_nonneg p r hp0 hpsum hr0 hrs
  have hklq : 0 ≤ kl q r := kl_nonneg q r hq0 hqsum hr0 hrs
  have hident := entropy_mix_identity p q lam
  have hident' : entropy r =
      lam * entropy p + (1 - lam) * entropy q + lam * kl p r + (1 - lam) * kl q r := by
    simpa [r] using hident
  have hnonneg : 0 ≤ lam * kl p r + (1 - lam) * kl q r := by
    exact add_nonneg (mul_nonneg hlam0 hklp) (mul_nonneg (sub_nonneg.mpr hlam1) hklq)
  rw [hident']
  linarith

/-! ## 引理：KL 严格正（p ≠ q）
p、q 严格正概率向量且 p ≠ q ⟹ KL(p‖q) > 0。
由 `kl_nonneg`（≥ 0）+ `kl_zero_iff_eq`（= 0 ⟺ p = q）闭合：KL 非负且非零。-/

lemma kl_pos_of_ne {k : ℕ} (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) (hpq : p ≠ q) : 0 < kl p q := by
  have hnonneg : 0 ≤ kl p q := kl_nonneg p q hp0 hpsum hq0 hqsum
  have hneq : kl p q ≠ 0 := by
    intro hz
    exact hpq ((kl_zero_iff_eq p q hp0 hpsum hq0 hqsum).mp hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hneq)

/-! ## 定理四（加分）：严格凹性
p ≠ q、lam ∈ (0,1) ⟹ H(r) > lam·H(p) + (1−lam)·H(q)。
由恒等式：差值 = lam·KL(p‖r) + (1−lam)·KL(q‖r)；
p ≠ q ⟹ p ≠ r（否则 (1−lam)(p − q) = 0，而 1−lam > 0），故 KL(p‖r) > 0
（`kl_pos_of_ne`），乘 lam > 0 加非负项 ⟹ 差值 > 0。-/

theorem entropy_concavity_strict {k : ℕ} (p q : Fin k → ℝ) (lam : ℝ)
    (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hpq : p ≠ q) :
    lam * entropy p + (1 - lam) * entropy q < entropy (mix lam p q) := by
  let r : Fin k → ℝ := mix lam p q
  have hpmf : (∀ a, 0 < mix lam p q a) ∧ ∑ a, mix lam p q a = 1 :=
    mix_pmf_strict lam p q (le_of_lt hlam0) (le_of_lt hlam1) hp0 hpsum hq0 hqsum
  have hr0 : ∀ a, 0 < r a := by
    intro a
    exact (hpmf.1) a
  have hrs : ∑ a, r a = 1 := hpmf.2
  -- p ≠ r：否则 p = lam·p + (1−lam)·q 逐点 ⟹ (1−lam)(p − q) = 0 ⟹ p = q，矛盾
  have hpne_r : p ≠ r := by
    intro hpr
    apply hpq
    funext a
    have hpa : p a = r a := congrFun hpr a
    have hra : r a = lam * p a + (1 - lam) * q a := by rfl
    have hmain : p a = lam * p a + (1 - lam) * q a := by rwa [hra] at hpa
    have hmul : (1 - lam) * p a = (1 - lam) * q a := by
      calc
        (1 - lam) * p a = p a - lam * p a := by ring
        _ = (lam * p a + (1 - lam) * q a) - lam * p a := by
              nth_rewrite 1 [hmain]
              rfl
        _ = (1 - lam) * q a := by ring
    have hsub : (1 - lam) * (p a - q a) = 0 := by
      rw [mul_sub, hmul, sub_self]
    rcases (mul_eq_zero.mp hsub) with h1 | hdiff
    · exfalso
      exact (sub_ne_zero.mpr (Ne.symm (ne_of_lt hlam1))) h1
    · exact sub_eq_zero.mp hdiff
  have hklp_pos : 0 < kl p r := kl_pos_of_ne p r hp0 hpsum hr0 hrs hpne_r
  have hklq_nonneg : 0 ≤ kl q r := kl_nonneg q r hq0 hqsum hr0 hrs
  have hident := entropy_mix_identity p q lam
  have hident' : entropy r =
      lam * entropy p + (1 - lam) * entropy q + lam * kl p r + (1 - lam) * kl q r := by
    simpa [r] using hident
  have hgt : 0 < lam * kl p r + (1 - lam) * kl q r := by
    have h1 : 0 < lam * kl p r := mul_pos hlam0 hklp_pos
    have h2 : 0 ≤ (1 - lam) * kl q r := mul_nonneg (sub_nonneg.mpr (le_of_lt hlam1)) hklq_nonneg
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_right h2)
  rw [hident']
  linarith

/-! ## 定理五（加分）：凹性的等式刻画
H(r) = lam·H(p) + (1−lam)·H(q) ⟺ lam ∈ {0,1} ∨ p = q（lam ∈ [0,1]）。
正向：0 < lam < 1 时差值 = lam·KL(p‖r) + (1−lam)·KL(q‖r) = 0 且两项非负
⟹ 各自为零（`sum_eq_zero` 思想 + `le_antisymm`）⟹ p = r = q（`kl_zero_iff_eq`）；
lam 退化或 p = q 时等式平凡成立（混合就是分量本身或两边都是 H(p)）。-/

theorem entropy_concavity_eq_iff {k : ℕ} (p q : Fin k → ℝ) (lam : ℝ)
    (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    entropy (mix lam p q) = lam * entropy p + (1 - lam) * entropy q
      ↔ lam = 0 ∨ lam = 1 ∨ p = q := by
  constructor
  · intro heq
    by_cases h0 : lam = 0
    · exact Or.inl h0
    · right
      by_cases h1 : lam = 1
      · exact Or.inl h1
      · right
        -- 0 < lam < 1
        have hlamgt : 0 < lam := lt_of_le_of_ne hlam0 (by intro hz; exact h0 hz.symm)
        have hlamlt : lam < 1 := lt_of_le_of_ne hlam1 h1
        let r : Fin k → ℝ := mix lam p q
        have hpmf : (∀ a, 0 < mix lam p q a) ∧ ∑ a, mix lam p q a = 1 :=
          mix_pmf_strict lam p q (le_of_lt hlamgt) (le_of_lt hlamlt) hp0 hpsum hq0 hqsum
        have hr0 : ∀ a, 0 < r a := by
          intro a
          exact (hpmf.1) a
        have hrs : ∑ a, r a = 1 := hpmf.2
        have hident := entropy_mix_identity p q lam
        have hident' : entropy r =
            lam * entropy p + (1 - lam) * entropy q + lam * kl p r + (1 - lam) * kl q r := by
          simpa [r] using hident
        have h : entropy r = lam * entropy p + (1 - lam) * entropy q := by
          simpa [r] using heq
        -- 差值 = lam·KL(p‖r) + (1−lam)·KL(q‖r) = 0
        have hdiff : lam * kl p r + (1 - lam) * kl q r = 0 := by
          rw [hident'] at h
          linarith
        have hklp0 : 0 ≤ kl p r := kl_nonneg p r hp0 hpsum hr0 hrs
        have hklq0 : 0 ≤ kl q r := kl_nonneg q r hq0 hqsum hr0 hrs
        -- 两项非负和为 0 ⟹ 各自为 0
        have hterm1 : lam * kl p r = 0 := by
          have hle1 : lam * kl p r ≤ lam * kl p r + (1 - lam) * kl q r :=
            le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (le_of_lt hlamlt)) hklq0)
          have hle1' : lam * kl p r ≤ 0 := by rwa [hdiff] at hle1
          exact le_antisymm hle1' (mul_nonneg (le_of_lt hlamgt) hklp0)
        have hklp_eq0 : kl p r = 0 := (mul_eq_zero.mp hterm1).resolve_left (ne_of_gt hlamgt)
        have hterm2 : (1 - lam) * kl q r = 0 := by
          have hle2 : (1 - lam) * kl q r ≤ lam * kl p r + (1 - lam) * kl q r :=
            le_add_of_nonneg_left (mul_nonneg (le_of_lt hlamgt) hklp0)
          have hle2' : (1 - lam) * kl q r ≤ 0 := by rwa [hdiff] at hle2
          exact le_antisymm hle2' (mul_nonneg (sub_nonneg.mpr (le_of_lt hlamlt)) hklq0)
        have hklq_eq0 : kl q r = 0 :=
          (mul_eq_zero.mp hterm2).resolve_left (sub_ne_zero.mpr (Ne.symm (ne_of_lt hlamlt)))
        have hp_r : p = r := (kl_zero_iff_eq p r hp0 hpsum hr0 hrs).mp hklp_eq0
        have hq_r : q = r := (kl_zero_iff_eq q r hq0 hqsum hr0 hrs).mp hklq_eq0
        exact hp_r.trans hq_r.symm
  · intro h
    rcases h with h0 | h1 | hpq
    · -- lam = 0：r = q，两边都等于 H(q)
      subst lam
      have hmix : mix 0 p q = q := by
        funext a
        simp [mix]
      rw [hmix]
      simp
    · -- lam = 1：r = p，两边都等于 H(p)
      subst lam
      have hmix : mix 1 p q = p := by
        funext a
        simp [mix]
      rw [hmix]
      simp
    · -- p = q：混合就是 p 本身，凸组合权重和为 1
      rw [hpq]
      have hmix : mix lam q q = q := by
        funext a
        unfold mix
        ring
      rw [hmix]
      ring

end Lattice
