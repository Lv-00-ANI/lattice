import Mathlib
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: 交叉熵 —— 信息论性质与 softmax 交叉熵梯度（训练线延伸）

RealAttention 给出 softmax（行随机概率分布：`softmax_nonneg`、`softmax_sum_one`），
本文件在其上建立**交叉熵损失**的信息论性质，并衔接分类训练：

  1. `crossEntropy p q = -Σ_a p a · log(q a)`（定义；log 定义域假设 `0 < q a`）；
  2. `ce_nonneg`：p、q 概率向量且 `0 < q a` ⟹ `0 ≤ CE(p,q)`
     （log 不等式 `Real.log_le_sub_one_of_pos`：log x ≤ x − 1 ⟹ −log x ≥ 1 − x，逐项 + 求和）；
  3. `entropy_nonneg`：H(p) = CE(p,p) ≥ 0（引理 1 特例，`0 < p a`）；
  4. `ce_onehot_eq_neg_log`：CE(onehot_y, q) = −log(q_y)
     （one-hot 求和只剩一项：`Finset.sum_eq_single`）；
  5. `ce_eq_zero_iff_support`：CE(p,q) = 0 ⟺ ∀ a, p a = 0 ∨ q a = 1
     （诚实版本——「CE(p,q)=0 ⟺ p=q」在严格正 q 下**不是定理**，见「诚实边界」）；
  6. `ce_eq_zero_of_onehot`：CE(onehot_y, q) = 0 ⟺ q_y = 1
     （分类损失为零 ⟺ 模型对真类概率为 1）；
  7. `ce_ge_entropy`（Gibbs）：H(p) ≤ CE(p,q)（KL(p‖q) = CE − H ≥ 0）；
  8. 梯度恒等式：L(s) = −log(softmax(s)_y)，fderiv L s v = Σ_j softmax(s)_j·v_j − v_y
     （经典 softmax 交叉熵梯度 ⟨softmax(s) − e_y, v⟩；
     `softmax_ce_fderiv_apply` + 方向导数版 `softmax_ce_directional_deriv`）。

**诚实边界**（本文件不证 / 不声称的）：
- 「CE(p,q) = 0 ⟺ p = q」**不是定理**：p = q 时 CE(p,q) = H(p)，非退化概率向量熵 > 0
  （如均匀分布 H = log k > 0）；且 mathlib 的 `Real.log` 在非正处取 0（全函数），
  q 含零时 CE 还会退化。故以 `ce_eq_zero_iff_support`（代数刻画）+
  `ce_eq_zero_of_onehot`（分类意义）取代。
- 梯度恒等式的任务稿符号为 v_y − Σ_j softmax_j·v_j，与经典
  ⟨softmax − e_y, v⟩ = Σ_j softmax_j·v_j − v_y **相反**；本文件按正确符号陈述。
- fderiv 采用方向导数桥（`fderiv_apply_direction_fin`，同 RealNormalEquation）；
  fderiv 的显式线性映射闭式未展开，只给作用形式（对偶配对）。
- `ce_onehot_eq_neg_log` 的 `0 < q y` 假设在 mathlib 的全函数 log 下并非证明所需，
  仅作 log 定义域的语义标注。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 定义：one-hot 标签、交叉熵、熵 -/

/-- one-hot 标签向量：onehot y a = 1（a = y），否则 0。-/
def onehot {k : ℕ} (y : Fin k) : Fin k → ℝ := fun a => if a = y then 1 else 0

/-- 交叉熵 CE(p,q) = -Σ_a p a · log(q a)（q 需在 log 定义域内，即 0 < q a）。-/
noncomputable def crossEntropy {k : ℕ} (p q : Fin k → ℝ) : ℝ := -∑ a, p a * Real.log (q a)

/-- 熵 H(p) = CE(p,p) = -Σ p·log p。-/
noncomputable def entropy {k : ℕ} (p : Fin k → ℝ) : ℝ := crossEntropy p p

/-! ## softmax 坐标严格正（log 复合的定义域前提） -/

lemma softmax_pos {k : ℕ} (z : Fin k → ℝ) : ∀ i, 0 < softmax z i := by
  intro i
  haveI : Nonempty (Fin k) := ⟨i⟩
  unfold softmax
  exact div_pos (Real.exp_pos (z i)) (softmax_denom_pos z)

/-! ## 引理：CE 的逐项形式
CE(p,q) = Σ_a p a·(−log q a)（把负号放进和里，便于逐项不等式）。-/

lemma ce_sum_neg (p q : Fin k → ℝ) : crossEntropy p q = ∑ a, p a * (-Real.log (q a)) := by
  calc
    crossEntropy p q = -∑ a, p a * Real.log (q a) := rfl
    _ = ∑ a, -(p a * Real.log (q a)) := by rw [← Finset.sum_neg_distrib]
    _ = ∑ a, p a * (-Real.log (q a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_neg]

/-! ## 定理一：交叉熵非负
p、q 概率向量且 0 < q a ⟹ 0 ≤ CE(p,q)。
路线：−log x ≥ 1 − x（`Real.log_le_sub_one_of_pos` 的推论）+ Σ p_a(1−q_a) = 1 − Σ p_a·q_a ≥ 0
（q_a ≤ 1：概率向量单一项 ≤ 和）。-/

theorem ce_nonneg (p q : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) : 0 ≤ crossEntropy p q := by
  -- q_a ≤ 1（概率向量：单一项 ≤ 和）
  have hq1 : ∀ a, q a ≤ 1 := by
    intro a
    have hle : q a ≤ ∑ b, q b :=
      Finset.single_le_sum (fun b hb => le_of_lt (hq0 b)) (Finset.mem_univ a)
    rwa [hqsum] at hle
  -- 逐项：1 − q_a ≤ −log q_a（log 不等式）
  have hneg : ∀ a, 1 - q a ≤ -Real.log (q a) := by
    intro a
    have hlog : Real.log (q a) ≤ q a - 1 := Real.log_le_sub_one_of_pos (hq0 a)
    linarith
  -- Σ p_a·q_a ≤ Σ p_a = 1
  have hpq : ∑ a, p a * q a ≤ 1 := by
    calc
      ∑ a, p a * q a ≤ ∑ a, p a * 1 := by
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (hq1 a) (hp0 a)
      _ = ∑ a, p a := by simp
      _ = 1 := hpsum
  -- Σ p_a(1−q_a) = 1 − Σ p_a·q_a
  have hsum1 : ∑ a, p a * (1 - q a) = 1 - ∑ a, p a * q a := by
    calc
      ∑ a, p a * (1 - q a) = ∑ a, (p a - p a * q a) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = (∑ a, p a) - ∑ a, p a * q a := by rw [Finset.sum_sub_distrib]
      _ = 1 - ∑ a, p a * q a := by rw [hpsum]
  -- Σ p_a(1−q_a) ≤ Σ p_a(−log q_a)（逐项）
  have hstep : ∑ a, p a * (1 - q a) ≤ ∑ a, p a * (-Real.log (q a)) := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (hneg a) (hp0 a)
  calc
    0 ≤ ∑ a, p a * (1 - q a) := by
          rw [hsum1]
          linarith [hpq]
    _ ≤ ∑ a, p a * (-Real.log (q a)) := hstep
    _ = crossEntropy p q := (ce_sum_neg p q).symm

/-! ## 定理二：熵非负
H(p) = CE(p,p) ≥ 0（0 < p a，log 定义域）。-/

theorem entropy_nonneg (p : Fin k → ℝ) (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1) :
    0 ≤ entropy p := by
  unfold entropy
  exact ce_nonneg p p (fun a => le_of_lt (hp0 a)) hpsum hp0 hpsum

/-! ## 定理三：one-hot 标签的 CE 只剩一项
CE(onehot_y, q) = −log(q_y)（`Finset.sum_eq_single`：a ≠ y 项为零）。
**第 213 轮删掉了前提 `(_hq : 0 < q y)`。** 本文件的 docstring 早就写着它是「log 定义域标注（mathlib 的 log 是全函数，证明并不需要）」——**承认了却留着，就是「说得比该说的弱」**。现在它与承认一致。 -/

theorem ce_onehot_eq_neg_log (y : Fin k) (q : Fin k → ℝ) :
    crossEntropy (onehot y) q = -Real.log (q y) := by
  have hsum : ∑ a, onehot y a * Real.log (q a) = Real.log (q y) := by
    rw [Finset.sum_eq_single y (by
      intro b hb hby
      simp [onehot, hby]) (by
      intro hy
      exact False.elim (hy (Finset.mem_univ y)))]
    simp [onehot]
  calc
    crossEntropy (onehot y) q = -∑ a, onehot y a * Real.log (q a) := rfl
    _ = -Real.log (q y) := by rw [hsum]

/-! ## 定理四：CE = 0 的代数刻画（诚实版本）
CE(p,q) = 0 ⟺ ∀ a, p a = 0 ∨ q a = 1
（p 非负、q 严格正概率向量）。注意这不是「CE=0 ⟺ p=q」——后者在严格正 q 下为假：
p=q 非退化时 CE(p,p)=H(p)>0。证明：每项 p_a·(−log q_a) ≥ 0（q_a ≤ 1 ⟹ log q_a ≤ 0），
非负和为零 ⟹ 每项为零 ⟹ p_a = 0 或 log q_a = 0（`Real.log_eq_zero` ⟺ q_a = 1）。-/

theorem ce_eq_zero_iff_support (p q : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) :
    crossEntropy p q = 0 ↔ ∀ a, p a = 0 ∨ q a = 1 := by
  -- q_a ≤ 1（概率向量）
  have hq1 : ∀ a, q a ≤ 1 := by
    intro a
    have hle : q a ≤ ∑ b, q b :=
      Finset.single_le_sum (fun b hb => le_of_lt (hq0 b)) (Finset.mem_univ a)
    rwa [hqsum] at hle
  -- 每项非负：p_a·(−log q_a) ≥ 0
  have hterm0 : ∀ a, 0 ≤ p a * (-Real.log (q a)) := by
    intro a
    apply mul_nonneg (hp0 a)
    have hlogle : Real.log (q a) ≤ 0 := by
      have hle : Real.log (q a) ≤ Real.log (1 : ℝ) :=
        Real.log_le_log (hq0 a) (hq1 a)
      rwa [Real.log_one] at hle
    linarith
  constructor
  · intro hce
    have hsum0 : ∑ a, p a * (-Real.log (q a)) = 0 := by
      rw [← ce_sum_neg p q, hce]
    have hz : ∀ a, p a * (-Real.log (q a)) = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hterm0 a)).mp hsum0
      intro a
      exact hall a (Finset.mem_univ a)
    intro a
    have hmul := mul_eq_zero.mp (hz a)
    rcases hmul with hpa | hlogz
    · exact Or.inl hpa
    · right
      have hlog : Real.log (q a) = 0 := by linarith
      rcases (Real.log_eq_zero.mp hlog) with hz | h1 | hn
      · exfalso
        linarith [hq0 a]
      · exact h1
      · exfalso
        linarith [hq0 a]
  · intro hsupp
    have hall : ∀ a, p a * (-Real.log (q a)) = 0 := by
      intro a
      rcases hsupp a with hpa | hqa
      · rw [hpa]
        simp
      · have hlog : Real.log (q a) = 0 := by rw [hqa, Real.log_one]
        simp [hlog]
    rw [ce_sum_neg p q]
    apply Finset.sum_eq_zero
    intro a ha
    exact hall a

/-! ## 定理五：one-hot 分类损失为零 ⟺ 真类概率为 1
CE(onehot_y, q) = 0 ⟺ q_y = 1（由 ce_onehot_eq_neg_log + log 零点）。-/

theorem ce_eq_zero_of_onehot (y : Fin k) (q : Fin k → ℝ) (hq : 0 < q y) :
    crossEntropy (onehot y) q = 0 ↔ q y = 1 := by
  rw [ce_onehot_eq_neg_log y q]
  constructor
  · intro h
    have hlog : Real.log (q y) = 0 := by linarith
    rcases (Real.log_eq_zero.mp hlog) with hz | h1 | hn
    · exfalso
      linarith [hq]
    · exact h1
    · exfalso
      linarith [hq]
  · intro hq1
    rw [hq1, Real.log_one]
    simp

/-! ## 定理六：分类训练损失 = 真类 softmax 概率的负对数
CE(onehot_y, softmax s) = −log(softmax s y)（训练线衔接：CE 即标准分类损失）。-/

theorem ce_onehot_softmax_eq_neg_log (s : Fin k → ℝ) (y : Fin k) :
    crossEntropy (onehot y) (softmax s) = -Real.log (softmax s y) := by
  haveI : Nonempty (Fin k) := ⟨y⟩
  exact ce_onehot_eq_neg_log y (softmax s)

/-! ## 定理七：Gibbs 不等式（CE ≥ H，KL 非负）
H(p) ≤ CE(p,q)（p、q 严格正概率向量）。
路线：CE − H = Σ p_a(log p_a − log q_a) ≥ Σ p_a(1 − q_a/p_a) = Σ(p_a − q_a) = 0
（log 不等式 at x = q_a/p_a：log(q/p) ≤ q/p − 1 ⟹ log p − log q ≥ 1 − q/p）。-/

theorem ce_ge_entropy (p q : Fin k → ℝ) (hp0 : ∀ a, 0 < p a) (hpsum : ∑ a, p a = 1)
    (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) :
    entropy p ≤ crossEntropy p q := by
  -- CE(p,q) − CE(p,p) = Σ p_a(log p_a − log q_a)
  have hdecomp : crossEntropy p q - crossEntropy p p
      = ∑ a, p a * (Real.log (p a) - Real.log (q a)) := by
    rw [ce_sum_neg p q, ce_sum_neg p p]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  -- 逐项下界：p_a − q_a ≤ p_a(log p_a − log q_a)
  have hterm : ∀ a, p a - q a ≤ p a * (Real.log (p a) - Real.log (q a)) := by
    intro a
    have hlogsep : 1 - q a / p a ≤ Real.log (p a) - Real.log (q a) := by
      have hpos : 0 < q a / p a := div_pos (hq0 a) (hp0 a)
      have hlogle : Real.log (q a / p a) ≤ q a / p a - 1 :=
        Real.log_le_sub_one_of_pos hpos
      have hsep : Real.log (q a) - Real.log (p a) = Real.log (q a / p a) := by
        rw [Real.log_div (ne_of_gt (hq0 a)) (ne_of_gt (hp0 a))]
      linarith
    have hmul : p a * (1 - q a / p a) ≤ p a * (Real.log (p a) - Real.log (q a)) :=
      mul_le_mul_of_nonneg_left hlogsep (le_of_lt (hp0 a))
    have heq : p a * (1 - q a / p a) = p a - q a := by
      field_simp [ne_of_gt (hp0 a)]
    rwa [heq] at hmul
  -- Σ(p_a − q_a) = 1 − 1 = 0
  have hsumdiff : ∑ a, (p a - q a) = 0 := by
    rw [Finset.sum_sub_distrib, hpsum, hqsum]
    simp
  have hle : crossEntropy p p ≤ crossEntropy p q := by
    have h0 : 0 ≤ crossEntropy p q - crossEntropy p p := by
      rw [hdecomp]
      have hsumle : ∑ a, (p a - q a) ≤ ∑ a, p a * (Real.log (p a) - Real.log (q a)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hterm a
      calc
        0 ≤ ∑ a, (p a - q a) := by rw [hsumdiff]
        _ ≤ ∑ a, p a * (Real.log (p a) - Real.log (q a)) := hsumle
    linarith
  unfold entropy
  exact hle

/-! ## softmax 交叉熵梯度（加分项）
L(s) = −log(softmax(s)_y)：分类交叉熵损失作为 logits 的函数。
方向导数：deriv (fun t => L(s + t·v)) 0 = Σ_j softmax(s)_j·v_j − v_y；
fderiv 版（方向导数桥）同值。
注意任务稿符号 v_y − Σ_j softmax_j·v_j 与经典 ⟨softmax − e_y, v⟩ 相反，
本文件按正确符号（Σ_j softmax_j·v_j − v_y）陈述。 -/

/-! ### 引理：fderiv 作用 = 方向导数（桥）
同 RealNormalEquation.fderiv_apply_direction，特化为 Fin k → ℝ。-/

lemma fderiv_apply_direction_fin {k : ℕ} {f : (Fin k → ℝ) → ℝ} {s v : Fin k → ℝ}
    (hf : DifferentiableAt ℝ f s) :
    fderiv ℝ f s v = deriv (fun t : ℝ => f (s + t • v)) 0 := by
  have hg : HasDerivAt (fun t : ℝ => s + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add s
  have hf' : HasFDerivAt f (fderiv ℝ f s) (s + (0 : ℝ) • v) := by
    have hs : s + (0 : ℝ) • v = s := by simp
    rw [hs]
    exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt 0 hg).deriv.symm

/-! ### 引理：L(s) = −log(softmax s y) 处处可导 -/

lemma softmax_ce_differentiableAt {k : ℕ} (s : Fin k → ℝ) (y : Fin k) :
    DifferentiableAt ℝ (fun z : Fin k → ℝ => -Real.log (softmax z y)) s := by
  haveI : Nonempty (Fin k) := ⟨y⟩
  -- 分子 exp(z y)、分母 Z(z) = Σ exp(z j) 都可导，分母非零（softmax_denom_pos）
  have hnum : DifferentiableAt ℝ (fun z : Fin k → ℝ => Real.exp (z y)) s := by
    have hproj : DifferentiableAt ℝ (fun z : Fin k → ℝ => z y) s := by
      simpa using (differentiableAt_apply (y : Fin k) s)
    exact hproj.exp
  have hden : DifferentiableAt ℝ (fun z : Fin k → ℝ => ∑ j : Fin k, Real.exp (z j)) s := by
    have hfd : ∀ j : Fin k, HasFDerivAt (fun z : Fin k → ℝ => Real.exp (z j))
        (fderiv ℝ (fun z : Fin k → ℝ => Real.exp (z j)) s) s := by
      intro j
      have hproj : DifferentiableAt ℝ (fun z : Fin k → ℝ => z j) s := by
        simpa using (differentiableAt_apply (j : Fin k) s)
      exact (hproj.exp).hasFDerivAt
    exact (HasFDerivAt.sum (by intro j hj; exact hfd j)).differentiableAt
  have hsm : DifferentiableAt ℝ (fun z : Fin k → ℝ => softmax z y) s := by
    have hne : (∑ j : Fin k, Real.exp (s j)) ≠ 0 := ne_of_gt (softmax_denom_pos s)
    -- softmax z y = exp(z y) / Z(z) = exp(z y)·Z(z)⁻¹：
    -- 分母可导（hden）⟹ 倒数可导（DifferentiableAt.inv）⟹ 乘积可导
    have hinv : DifferentiableAt ℝ (fun z : Fin k → ℝ => (∑ j : Fin k, Real.exp (z j))⁻¹) s :=
      hden.inv hne
    have hprod : DifferentiableAt ℝ (fun z : Fin k → ℝ => Real.exp (z y) * (∑ j : Fin k, Real.exp (z j))⁻¹) s :=
      hnum.mul hinv
    simpa [softmax] using hprod
  have hlog : DifferentiableAt ℝ (fun z : Fin k → ℝ => Real.log (softmax z y)) s := by
    exact (hsm.hasFDerivAt.log (ne_of_gt (softmax_pos s y))).differentiableAt
  exact hlog.neg

/-! ### 定理八：softmax 交叉熵的方向导数
deriv (fun t => −log(softmax(s + t·v)_y)) 0 = Σ_j softmax(s)_j·v_j − v_y。
路线：商法则（exp 分子 + Z 分母）⟹ softmax 坐标导数 = sm_y·(v_y − Σ sm_j·v_j)，
log 链式（Real.hasDerivAt_log）⟹ 取负。 -/

theorem softmax_ce_directional_deriv (s v : Fin k → ℝ) (y : Fin k) :
    deriv (fun t : ℝ => -Real.log (softmax (s + t • v) y)) 0
      = (∑ j, softmax s j * v j) - v y := by
  haveI : Nonempty (Fin k) := ⟨y⟩
  have hsmpos : 0 < softmax s y := softmax_pos s y
  -- 分子 exp(s_y + t·v_y) 的导数：exp(s_y)·v_y
  have hnum : HasDerivAt (fun t : ℝ => Real.exp (s y + t * v y)) (Real.exp (s y) * v y) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => s y + t * v y) (v y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v y)).const_add (s y)
    have hc : HasDerivAt (fun t : ℝ => Real.exp (s y + t * v y))
        (Real.exp (s y + 0 * v y) * v y) 0 :=
      (Real.hasDerivAt_exp (s y + 0 * v y)).comp 0 hlin
    simpa using hc
  -- 分母 Z(t) = Σ exp(s_j + t·v_j) 的导数：Σ exp(s_j)·v_j
  have htermZ : ∀ j : Fin k, HasDerivAt (fun t : ℝ => Real.exp (s j + t * v j))
      (Real.exp (s j) * v j) 0 := by
    intro j
    have hlin : HasDerivAt (fun t : ℝ => s j + t * v j) (v j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (s j)
    have hc : HasDerivAt (fun t : ℝ => Real.exp (s j + t * v j))
        (Real.exp (s j + 0 * v j) * v j) 0 :=
      (Real.hasDerivAt_exp (s j + 0 * v j)).comp 0 hlin
    simpa using hc
  have hZ : HasDerivAt (fun t : ℝ => ∑ j : Fin k, Real.exp (s j + t * v j))
      (∑ j : Fin k, Real.exp (s j) * v j) 0 := by
    exact HasDerivAt.sum (by intro j hj; exact htermZ j)
  have hZ0 : 0 < ∑ j : Fin k, Real.exp (s j + 0 * v j) := by
    simpa using (softmax_denom_pos (z := s))
  -- 商法则
  have hq0 := hnum.div hZ (ne_of_gt hZ0)
  -- 商函数导数的化简：messy 商式 = sm_y·(v_y − Σ sm_j·v_j)
  have hsimpl : (Real.exp (s y) * v y * (∑ j : Fin k, Real.exp (s j))
        - Real.exp (s y) * (∑ j : Fin k, Real.exp (s j) * v j))
        / (∑ j : Fin k, Real.exp (s j)) ^ 2
      = softmax s y * (v y - ∑ j, softmax s j * v j) := by
    let Z : ℝ := ∑ j : Fin k, Real.exp (s j)
    let S : ℝ := ∑ j : Fin k, Real.exp (s j) * v j
    have hZne : Z ≠ 0 := by
      simpa [Z] using (ne_of_gt (softmax_denom_pos (z := s)))
    have hS : S / Z = ∑ j : Fin k, (Real.exp (s j) / Z) * v j := by
      change ((∑ j : Fin k, Real.exp (s j) * v j) / Z) = ∑ j : Fin k, (Real.exp (s j) / Z) * v j
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hZsimp : (Real.exp (s y) * v y * Z - Real.exp (s y) * S) / Z ^ 2
        = softmax s y * (v y - ∑ j, softmax s j * v j) := by
      calc
        (Real.exp (s y) * v y * Z - Real.exp (s y) * S) / Z ^ 2
            = (Real.exp (s y) / Z) * (v y - S / Z) := by
              field_simp [hZne]
              ring
        _ = (Real.exp (s y) / Z) * (v y - ∑ j, (Real.exp (s j) / Z) * v j) := by rw [hS]
        _ = softmax s y * (v y - ∑ j, softmax s j * v j) := by
              simp [Z, softmax]
    simpa [Z, S] using hZsimp
  -- 商函数在 0 处的 deriv 值
  have hqderiv : deriv (fun t : ℝ => Real.exp (s y + t * v y) / (∑ j : Fin k, Real.exp (s j + t * v j))) 0
      = softmax s y * (v y - ∑ j, softmax s j * v j) := by
    rw [hq0.deriv]
    simp
    exact hsimpl
  have hq : HasDerivAt (fun t : ℝ => Real.exp (s y + t * v y) / (∑ j : Fin k, Real.exp (s j + t * v j)))
      (softmax s y * (v y - ∑ j, softmax s j * v j)) 0 := by
    simpa [hqderiv] using hq0.differentiableAt.hasDerivAt
  -- 换到 softmax 记号：(s + t·v) y = s y + t·v y
  have hf : HasDerivAt (fun t : ℝ => softmax (s + t • v) y)
      (softmax s y * (v y - ∑ j, softmax s j * v j)) 0 := by
    simpa [softmax, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hq
  -- log 链式（Real.hasDerivAt_log）⟹ 取负
  -- 注意 comp 的复合点：h 0 = softmax (s + (0:ℝ) • v) y，先证其等于 softmax s y
  have h0sm : softmax (s + (0 : ℝ) • v) y = softmax s y := by
    unfold softmax
    have hnum0 : Real.exp ((s + (0 : ℝ) • v) y) = Real.exp (s y) := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hden0 : (∑ j : Fin k, Real.exp ((s + (0 : ℝ) • v) j)) = ∑ j : Fin k, Real.exp (s j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp [hnum0, hden0]
  have hlogAt : HasDerivAt Real.log (softmax s y)⁻¹ (softmax (s + (0 : ℝ) • v) y) := by
    rw [h0sm]
    exact Real.hasDerivAt_log (ne_of_gt hsmpos)
  have hlog : HasDerivAt (fun t : ℝ => Real.log (softmax (s + t • v) y))
      ((softmax s y)⁻¹ * (softmax s y * (v y - ∑ j, softmax s j * v j))) 0 := by
    simpa using hlogAt.comp 0 hf
  have hneg : HasDerivAt (fun t : ℝ => -Real.log (softmax (s + t • v) y))
      (-((softmax s y)⁻¹ * (softmax s y * (v y - ∑ j, softmax s j * v j)))) 0 :=
    hlog.neg
  -- 化简：−((sm_y)⁻¹·(sm_y·X)) = Σ_j sm_j·v_j − v_y（X = v_y − Σ sm·v）
  have hcancel : (softmax s y)⁻¹ * (softmax s y * (v y - ∑ j, softmax s j * v j))
      = v y - ∑ j, softmax s j * v j := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsmpos), one_mul]
  rw [hneg.deriv]
  rw [hcancel]
  ring

/-! ### 定理九：softmax 交叉熵的 fderiv（对偶作用形式）
fderiv L s v = Σ_j softmax(s)_j·v_j − v_y = ⟨softmax(s) − e_y, v⟩
（方向导数桥 `fderiv_apply_direction_fin` + 定理八）。-/

theorem softmax_ce_fderiv_apply (s v : Fin k → ℝ) (y : Fin k) :
    fderiv ℝ (fun z : Fin k → ℝ => -Real.log (softmax z y)) s v
      = (∑ j, softmax s j * v j) - v y := by
  have hbridge : fderiv ℝ (fun z : Fin k → ℝ => -Real.log (softmax z y)) s v
      = deriv (fun t : ℝ => -Real.log (softmax (s + t • v) y)) 0 :=
    fderiv_apply_direction_fin (softmax_ce_differentiableAt s y)
  rw [hbridge]
  exact softmax_ce_directional_deriv s v y

/-! ### 推论：经典梯度形式 ⟨softmax(s) − e_y, v⟩
fderiv L s v = Σ_j (softmax(s)_j − δ_jy)·v_j，δ = onehot y。-/

theorem softmax_ce_fderiv_eq_dot (s v : Fin k → ℝ) (y : Fin k) :
    fderiv ℝ (fun z : Fin k → ℝ => -Real.log (softmax z y)) s v
      = ∑ j, (softmax s j - (if j = y then 1 else 0)) * v j := by
  rw [softmax_ce_fderiv_apply s v y]
  -- Σ (sm_j − δ_jy)·v_j = Σ sm_j·v_j − v_y（δ 项只剩 j = y）
  have hstep1 : ∑ j, (softmax s j - (if j = y then 1 else 0)) * v j
      = ∑ j, (softmax s j * v j - (if j = y then 1 else 0) * v j) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hstep2 : ∑ j, (softmax s j * v j - (if j = y then 1 else 0) * v j)
      = (∑ j, softmax s j * v j) - ∑ j, (if j = y then 1 else 0) * v j := by
    rw [Finset.sum_sub_distrib]
  have hone : ∑ j, (if j = y then 1 else 0) * v j = v y := by
    rw [Finset.sum_eq_single y (by
      intro b hb hby
      simp [hby]) (by
      intro hy
      exact False.elim (hy (Finset.mem_univ y)))]
    simp
  calc
    (∑ j, softmax s j * v j) - v y
        = (∑ j, softmax s j * v j) - ∑ j, (if j = y then 1 else 0) * v j := by rw [hone]
    _ = ∑ j, (softmax s j * v j - (if j = y then 1 else 0) * v j) := hstep2.symm
    _ = ∑ j, (softmax s j - (if j = y then 1 else 0)) * v j := hstep1.symm

/-! ## 注：训练线收官
CE（本文件：非负 + 熵 + one-hot 损失 + 梯度）连接 RealAttention 的 softmax
（概率分布）与训练/驻点线（RealPolicyGradient 的 log 导数、RealNormalEquation/
RealVectorStationarity 的 fderiv 桥）：softmax 交叉熵梯度 = softmax − one-hot 标签，
驻点 ⟹ softmax(s) = e_y ⟹ 模型把全部概率放在真类（过拟合/插值情形）。 -/

end Lattice
