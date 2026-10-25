import Mathlib
import Lattice.Lib.InfoTheory.RealCrossEntropy
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Convex.RealConvexToolkit
/-!
# LATTICE: KL 散度（相对熵）—— CE 与熵的桥接、非负性（Gibbs）、零化刻画

RealCrossEntropy 建立交叉熵 `crossEntropy`（CE(p,q) = −Σ p·log q）、熵 `entropy`
（H(p) = CE(p,p)）与 softmax 概率向量（`softmax_nonneg`/`softmax_sum_one`/`softmax_pos`）。
本文件在其上定义 **KL 散度（相对熵）** KL(p‖q) = CE(p,q) − H(p)，并建立：

  1. `kl_eq_ce_sub_entropy`：定义桥 KL(p‖q) = CE(p,q) − H(p)（rfl）；
  2. `kl_as_sum_log_ratio`：显式求和 KL(p‖q) = Σ_a p_a·log(p_a/q_a)
     （`Real.log_div` 把 log p − log q 合成 log(p/q)；log 定义域假设 0 < p、0 < q）；
  3. `kl_nonneg`：KL(p‖q) ≥ 0（Gibbs：由 `ce_ge_entropy`（H ≤ CE）直接得 CE − H ≥ 0）；
  4. `kl_zero_iff_support`：KL(p‖q) = 0 ⟺ ∀ a, p a = 0 ∨ q a = p a
     （p 非负、q 严格正概率向量下的**真实**代数刻画；见「诚实边界」）；
  5. `kl_zero_iff_eq`：p 严格正时 KL(p‖q) = 0 ⟺ p = q
     （KL 与 CE 不同：零化确实刻画分布相等——逐项 Gibbs 下界
     p_a·log(p_a/q_a) ≥ p_a − q_a 的等号情形由严格 log 不等式
     `Real.log_lt_sub_one_of_pos`（log x = 1 − x⁻¹ ⟹ x = 1）闭合）；
  6. `kl_eq_zero_of_eq`：p = q ⟹ KL(p‖q) = 0（平凡方向）；
  7. `kl_onehot`：KL(onehot_y ‖ q) = −log(q_y)
     （one-hot 求和只剩一项（`Finset.sum_eq_single`），熵项 H(onehot_y) = −log 1 = 0，
     衔接 `ce_onehot_eq_neg_log`）；
  8. `kl_softmax_pmf`：q = softmax s 时 KL(p‖softmax s) ≥ 0
     （softmax 是严格正概率向量：`softmax_pos` + `softmax_sum_one`，套用 `kl_nonneg`；
     `[Nonempty (Fin k)]` 是 softmax 的行随机性（Σ softmax = 1）所需的指标集非空前提）。

**诚实边界**（本文件不证 / 不声称的）：
- 「KL(p‖q) = 0 ⟺ p = q」在 p、q 均严格正时是**真**定理（`kl_zero_iff_eq`）；
  对 p 仅非负（q 严格正）的情形，真实刻画是 `kl_zero_iff_support`
  （∀ a, p a = 0 ∨ q a = p a：零质量的坐标不约束 q，正质量的坐标必须逐点相等）。
  这与 CE 不同——CE = 0 受 H(p) 污染（p = q 非退化时 CE(p,p) = H(p) > 0），
  KL 减去 H(p) 后零化才是真正的分布相等。
- mathlib 的 `Real.log` 是非正处取 0 的全函数；所有含 log 的等式均在
  0 < p a、0 < q a（log 定义域）的诚实假设下陈述，这是语义标注而非证明所需。
- 未做：KL 对参数的导数 / Fisher 信息、连续分布 KL、KL 的凸性（Jensen）；
  如需可后续文件承接。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 定义：KL 散度 = CE − H -/

/-- KL 散度（相对熵）：KL(p‖q) = CE(p,q) − H(p) = Σ_a p_a·log(p_a/q_a)。-/
noncomputable def kl {k : ℕ} (p q : Fin k → ℝ) : ℝ := crossEntropy p q - entropy p

/-- 定义桥：KL(p‖q) = CE(p,q) − H(p)（按定义即证）。-/
theorem kl_eq_ce_sub_entropy {k : ℕ} (p q : Fin k → ℝ) :
    kl p q = crossEntropy p q - entropy p := rfl

/-! ## 引理：KL 的逐项形式（无需假设，log 为全函数）
KL(p‖q) = Σ_a p_a·(log p_a − log q_a) = CE(p,q) − CE(p,p)。-/

lemma kl_as_sum_log_sub_log {k : ℕ} (p q : Fin k → ℝ) :
    kl p q = ∑ a, p a * (Real.log (p a) - Real.log (q a)) := by
  unfold kl entropy
  rw [ce_sum_neg p q, ce_sum_neg p p]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-! ## 引理：KL 的显式求和形式
KL(p‖q) = Σ_a p_a·log(p_a/q_a)（0 < p、0 < q：log 定义域；`Real.log_div` 合成）。-/

theorem kl_as_sum_log_ratio {k : ℕ} (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a)
    (hq0 : ∀ a, 0 < q a) : kl p q = ∑ a, p a * Real.log (p a / q a) := by
  rw [kl_as_sum_log_sub_log p q]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Real.log_div (ne_of_gt (hp0 a)) (ne_of_gt (hq0 a))]

/-! ## 定理一：KL 非负（Gibbs）
KL(p‖q) ≥ 0：由 `ce_ge_entropy`（H(p) ≤ CE(p,q)）直接得 CE − H ≥ 0。-/

theorem kl_nonneg {k : ℕ} (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) : 0 ≤ kl p q := by
  unfold kl
  have hge : entropy p ≤ crossEntropy p q := ce_ge_entropy p q hp0 hpsum hq0 hqsum
  linarith

/-! ## 引理：逐项 Gibbs 下界
p_a − q_a ≤ p_a·(log p_a − log q_a)（p 非负、q 严格正）。

**REFACTOR Step 3（v12）**：原 ~20 行独立证明已收敛到唯一权威位置
`RealConvexToolkit.gibbs_ineq`，此处保留 **同名兼容接口**（下游调用点无需改动）。
路线（权威层实现）：log 不等式 `Real.one_sub_inv_le_log_of_pos` at x = p/q：
1 − q/p ≤ log(p/q) = log p − log q，乘 p > 0；p_a = 0 时平凡（−q_a ≤ 0）。-/

lemma kl_term_ge {k : ℕ} (p q : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hq0 : ∀ a, 0 < q a) :
    ∀ a, p a - q a ≤ p a * (Real.log (p a) - Real.log (q a)) :=
  fun a => gibbs_ineq (hp0 a) (hq0 a)

/-! ## 定理二：KL = 0 的代数刻画（诚实版本）
KL(p‖q) = 0 ⟺ ∀ a, p a = 0 ∨ q a = p a
（p 非负、q 严格正概率向量）。证明：逐项 Gibbs 下界给出 Σ(p − q) = 0 ≤ KL，
KL = 0 ⟹ Σ[p·(log p − log q) − (p − q)] = 0，逐项非负和为零 ⟹ 每项为零；
p_a > 0 时 p_a·(log p_a − log q_a) = p_a − q_a ⟹ log(p_a/q_a) = 1 − (p_a/q_a)⁻¹
⟹ p_a/q_a = 1（严格 log 不等式 `Real.log_lt_sub_one_of_pos` 的等号情形）⟹ q_a = p_a。-/

theorem kl_zero_iff_support {k : ℕ} (p q : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) :
    kl p q = 0 ↔ ∀ a, p a = 0 ∨ q a = p a := by
  have hterm : ∀ a, p a - q a ≤ p a * (Real.log (p a) - Real.log (q a)) :=
    kl_term_ge p q hp0 hq0
  have hsumdiff : ∑ a, (p a - q a) = 0 := by
    rw [Finset.sum_sub_distrib, hpsum, hqsum]
    simp
  have hdiff0 : ∀ a, 0 ≤ p a * (Real.log (p a) - Real.log (q a)) - (p a - q a) := by
    intro a
    linarith [hterm a]
  constructor
  · intro hkl
    have hsum0 : ∑ a, (p a * (Real.log (p a) - Real.log (q a)) - (p a - q a)) = 0 := by
      rw [Finset.sum_sub_distrib, ← kl_as_sum_log_sub_log p q, hkl, hsumdiff]
      ring
    have hz : ∀ a, p a * (Real.log (p a) - Real.log (q a)) - (p a - q a) = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hdiff0 a)).mp hsum0
      intro a
      exact hall a (Finset.mem_univ a)
    intro a
    by_cases hpa : p a = 0
    · exact Or.inl hpa
    · right
      have hpa' : 0 < p a := lt_of_le_of_ne (hp0 a) (Ne.symm hpa)
      have heqterm : p a * (Real.log (p a) - Real.log (q a)) = p a - q a := by linarith [hz a]
      have hlogeq : Real.log (p a / q a) = 1 - (p a / q a)⁻¹ := by
        have hd : Real.log (p a) - Real.log (q a) = (p a - q a) / p a := by
          calc
            Real.log (p a) - Real.log (q a) = (p a * (Real.log (p a) - Real.log (q a))) / p a := by
              field_simp [ne_of_gt hpa']
            _ = (p a - q a) / p a := by rw [heqterm]
        have hd2 : (p a - q a) / p a = 1 - q a / p a := by field_simp [ne_of_gt hpa']
        have h1 : Real.log (p a) - Real.log (q a) = 1 - q a / p a := by
          rw [hd, hd2]
        have hinv : (p a / q a)⁻¹ = q a / p a := by simp
        have hsep : Real.log (p a / q a) = Real.log (p a) - Real.log (q a) := by
          rw [Real.log_div (ne_of_gt hpa') (ne_of_gt (hq0 a))]
        rw [← hsep] at h1
        rwa [← hinv] at h1
      have hxpos : 0 < p a / q a := div_pos hpa' (hq0 a)
      have hx1 : p a / q a = 1 := by
        by_contra hxne
        have hlt1 : Real.log (p a / q a) < p a / q a - 1 :=
          Real.log_lt_sub_one_of_pos hxpos hxne
        have hinvne : (p a / q a)⁻¹ ≠ 1 := by
          intro h
          have : p a / q a = 1 := by simpa using congrArg (fun t : ℝ => t⁻¹) h
          exact hxne this
        have hlt2 : Real.log ((p a / q a)⁻¹) < (p a / q a)⁻¹ - 1 :=
          Real.log_lt_sub_one_of_pos (inv_pos.mpr hxpos) hinvne
        have hloginv : Real.log ((p a / q a)⁻¹) = -Real.log (p a / q a) :=
          Real.log_inv (p a / q a)
        have hgt : 1 - (p a / q a)⁻¹ < Real.log (p a / q a) := by
          rw [hloginv] at hlt2
          linarith
        linarith
      have hpq : p a = q a := by
        calc
          p a = (p a / q a) * q a := by field_simp [ne_of_gt (hq0 a)]
          _ = 1 * q a := by rw [hx1]
          _ = q a := by ring
      exact hpq.symm
  · intro hsupp
    rw [kl_as_sum_log_sub_log p q]
    apply Finset.sum_eq_zero
    intro a ha
    rcases hsupp a with hpa | hqa
    · rw [hpa]
      simp
    · rw [hqa]
      ring

/-! ## 定理三：KL = 0 ⟺ p = q（p 严格正）
p 严格正概率向量时 `kl_zero_iff_support` 的零化刻画退化为逐点相等：
∀ a, p a = 0 ∨ q a = p a，而 p a > 0 ⟹ q a = p a。-/

theorem kl_zero_iff_eq {k : ℕ} (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a)
    (hpsum : ∑ a, p a = 1) (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) :
    kl p q = 0 ↔ p = q := by
  have hsupp : kl p q = 0 ↔ ∀ a, p a = 0 ∨ q a = p a :=
    kl_zero_iff_support p q (fun a => le_of_lt (hp0 a)) hpsum hq0 hqsum
  constructor
  · intro hkl
    have h : ∀ a, p a = 0 ∨ q a = p a := hsupp.mp hkl
    funext a
    rcases h a with hpa | hqa
    · exfalso
      linarith [hp0 a]
    · exact hqa.symm
  · intro hpq
    rw [hpq]
    unfold kl entropy
    ring

/-! ## 推论：p = q ⟹ KL(p‖q) = 0（平凡方向） -/

theorem kl_eq_zero_of_eq {k : ℕ} (p q : Fin k → ℝ) (hpq : p = q) : kl p q = 0 := by
  rw [hpq]
  unfold kl entropy
  ring

/-! ## 定理四：one-hot 标签的 KL 只剩一项
KL(onehot_y ‖ q) = CE(onehot_y, q) − H(onehot_y) = −log(q_y) − (−log 1) = −log(q_y)
（衔接 `ce_onehot_eq_neg_log`；`0 < q y` 为 log 定义域标注）。-/

theorem kl_onehot {k : ℕ} (y : Fin k) (q : Fin k → ℝ) (hq : 0 < q y) :
    kl (onehot y) q = -Real.log (q y) := by
  unfold kl entropy
  rw [ce_onehot_eq_neg_log y q hq]
  have hq1 : 0 < onehot y y := by simp [onehot]
  rw [ce_onehot_eq_neg_log y (onehot y) hq1]
  simp [onehot, Real.log_one]

/-! ## 定理五（加分）：softmax 概率向量的 KL 非负
q = softmax s 是严格正概率向量（`softmax_pos` + `softmax_sum_one`），
套用 `kl_nonneg` 得 KL(p‖softmax s) ≥ 0。
`[Nonempty (Fin k)]`：softmax 的行随机性（Σ softmax = 1）需要非空指标集。-/

theorem kl_softmax_pmf {k : ℕ} [Nonempty (Fin k)] (p s : Fin k → ℝ)
    (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1) : 0 ≤ kl p (softmax s) := by
  have hq0 : ∀ a, 0 < softmax s a := softmax_pos s
  have hqsum : ∑ a, softmax s a = 1 := softmax_sum_one s
  exact kl_nonneg p (softmax s) hp0 hpsum hq0 hqsum

end Lattice
