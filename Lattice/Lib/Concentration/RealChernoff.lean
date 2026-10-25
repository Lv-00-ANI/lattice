import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.LearningTheory.RealSamplingBoost
/-!
# LATTICE: 乘性切尔诺夫界 —— 独立伯努利随机变量之和的乘性集中界

方向（§5 验证行「Chernoff」）：RealHoeffding 的 Hoeffding 界是**加性**指数集中界
（P(X̄ − μ ≥ t) ≤ e^{−nt²/8}，偏差按绝对量 t 度量）；本文件给出指数集中界家族的
最后一个经典成员——**乘性**切尔诺夫界：S = Σᵢ Xᵢ 是 n 个独立伯努利变量
（Xᵢ ∈ {0,1}、P(Xᵢ=1) = pᵢ）之和，μ = E[S] = Σᵢ pᵢ，则对 δ ∈ (0,1]：

  P(S ≥ (1+δ)·μ) ≤ e^{−δ²μ/3}（上尾，乘性偏差 (1+δ)μ 而非加性偏差 t）

对 δ ∈ (0,1) 还有下尾 P(S ≤ (1−δ)·μ) ≤ e^{−δ²μ/2}，以及双边
P(|S − μ| ≥ δ·μ) ≤ 2·e^{−δ²μ/3}。

**设定（有限计数概率空间，完全继承 RealHoeffding / RealSamplingBoost）**：
样本空间 α 有限（Fintype），均匀概率 `uniformProb s = s.card / Fintype.card α`；
每个坐标 i 的伯努利变量是函数 `X i : α → ℝ`（取值 {0,1}，期望 `p i`）；
n 个独立副本 = 乘积空间 `Fin n → α`，独立性体现为 `Finset.prod_univ_sum` 的
乘积分解（同 RealHoeffding 的 `hoeffding_tail_bounded`）。

**定理链**：
1. `bernoulli_mgf_bound`（核心引理）：X ∈ {0,1}、E[X] = p ⟹ E[e^{λX}] ≤ e^{p(e^λ−1)}。
   E[e^{λX}] = (1−p)·1 + p·e^λ = 1 + p(e^λ−1) ≤ e^{p(e^λ−1)}（`Real.add_one_le_exp`，
   mathlib 既有：1+x ≤ e^x）。
2. `sum_mgf_factor`：独立和 S = Σᵢ Xᵢ 的矩生成 = ∏ᵢ E[e^{λXᵢ}]
   （`Finset.prod_univ_sum` + `Real.exp_sum`，同 Hoeffding 的乘积分解）。
3. `sum_mgf_le`：E[e^{λS}] ≤ e^{μ(e^λ−1)}（引理 1 × 乘积分解 × ∏e^{aᵢ} = e^{Σaᵢ}）。
4. `markov_exp_tail_neg`：切尔诺夫桥的下尾方向 P(S ≤ t) ≤ e^{λt}·E[e^{−λS}]
   （RealHoeffding 的 `markov_exp_tail` 是上尾方向 P(S ≥ t) ≤ e^{−λt}·E[e^{λS}]）。
5. `log_one_add_pade`（分析核心）：ln(1+δ) ≥ 2δ/(2+δ)（δ ∈ [0,1]，Padé 型下界）。
   证明：p(δ) = ln(1+δ) − 2δ/(2+δ)，p(0) = 0，p' = δ²/((1+δ)(2+δ)²) > 0 于 (0,1)，
   `strictMonoOn_of_deriv_pos`（mathlib 均值定理族）。
6. `chernoff_log_upper`：δ − (1+δ)·ln(1+δ) ≤ −δ²/3（δ ∈ [0,1]）。
   路线：由 Padé 下界 δ − (1+δ)ln(1+δ) ≤ δ − (1+δ)·2δ/(2+δ) = −δ²/(2+δ) ≤ −δ²/3。
   **常数 1/3 是经典锐常数**，无需保守化。
7. `log_le_half_sub_inv`：ln v ≤ (v − 1/v)/2（v ≥ 1）。证明：q(v) = (v−1/v)/2 − ln v，
   q(1) = 0，q' = (v−1)²/(2v²) > 0 于 (1,∞)，`strictMonoOn_of_deriv_pos`。
8. `chernoff_log_lower`：(1−δ)·ln(1/(1−δ)) − δ ≤ −δ²/2（δ ∈ [0,1)）。
   路线：ln(1/(1−δ)) ≤ (1/(1−δ) − (1−δ))/2（引理 7 代入 v = 1/(1−δ)）
   ⟹ (1−δ)·ln(1/(1−δ)) ≤ (1−(1−δ)²)/2 ⟹ 左边 − δ ≤ −δ²/2。**常数 1/2 是经典锐常数**。
9. `chernoff_upper_tail`（核心）：P(S ≥ (1+δ)μ) ≤ e^{−δ²μ/3}。路线：
   切尔诺夫桥（`markov_exp_tail`，λ = ln(1+δ)）+ `sum_mgf_le`
   ⟹ P ≤ e^{−λ(1+δ)μ + μ(e^λ−1)} = e^{μ(δ − (1+δ)ln(1+δ))} ≤ e^{−δ²μ/3}（引理 6）。
10. `chernoff_lower_tail`（加分）：P(S ≤ (1−δ)μ) ≤ e^{−δ²μ/2}（对称，λ = ln(1/(1−δ))）。
11. `chernoff_two_sided`（加分）：P(|S − μ| ≥ δμ) ≤ 2·e^{−δ²μ/3}（上尾 + 下尾 + 并集）。

**诚实假设与标注**：
- 上尾要求 δ ∈ (0,1]（经典陈述）；下尾/双边要求 δ ∈ (0,1)（(1−δ)μ > 0 与
  λ = ln(1/(1−δ)) 的正性需要 1−δ > 0；δ = 1 时事件退化为 S ≤ 0，本文件不覆盖）。
- 要求 0 < μ = Σᵢ pᵢ（μ = 0 时乘性界退化，P(S ≥ 0) = 1 ≤ e^0 平凡成立）。
- 要求 α 非空（N = |α| > 0，均匀概率分母非零）。
- **不使用 sorry / axiom / admit**；所有常数（上尾 1/3、下尾 1/2）均为经典锐常数，
  由引理 5/7 的 Padé/反双曲型对数下界给出（诚实证明，非保守估计）。
- 与 Hoeffding 的关系：Hoeffding 是加性界（偏差按绝对量，X ∈ [0,1] 时 e^{−2nt²}），
  切尔诺夫是乘性界（偏差按相对量 δμ）；本文件的 MGF 上界来自伯努利精确期望
  1 + p(e^λ−1) ≤ e^{p(e^λ−1)}（而非 Hoeffding 的 exp 凸性弦上界）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 引理 1（核心）：伯努利矩生成函数上界
X ∈ {0,1}（逐点）、E[X] = p ⟹ E[e^{λX}] ≤ e^{p(e^λ−1)}。
证明：逐点 e^{λX} = 1 + X(e^λ−1)（X ∈ {0,1}），取期望得 1 + p(e^λ−1)，
再用 mathlib 的 1+x ≤ e^x（`Real.add_one_le_exp`）。 -/

theorem bernoulli_mgf_bound {α : Type*} [Fintype α] {X : α → ℝ} {p lam : ℝ}
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = p)
    (hval : ∀ x : α, X x = 0 ∨ X x = 1) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (p * (Real.exp lam - 1)) := by
  -- 逐点：e^{λX} = 1 + X(e^λ − 1)（X ∈ {0,1}）
  have hpoint : ∀ x : α, Real.exp (lam * X x) = 1 + X x * (Real.exp lam - 1) := by
    intro x
    rcases hval x with h0 | h1
    · rw [h0, mul_zero, Real.exp_zero]
      norm_num
    · rw [h1, mul_one]
      ring
  have hsum : (∑ x : α, Real.exp (lam * X x)) =
      (∑ x : α, (1 + X x * (Real.exp lam - 1))) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact hpoint x
  -- 求和分解：∑(1 + X·c) = N + (∑X)·c
  have hsumR : (∑ x : α, (1 + X x * (Real.exp lam - 1))) =
      (Fintype.card α : ℝ) + (∑ x : α, X x) * (Real.exp lam - 1) := by
    calc
      (∑ x : α, (1 + X x * (Real.exp lam - 1)))
          = (∑ x : α, 1) + (∑ x : α, X x * (Real.exp lam - 1)) := by
            rw [Finset.sum_add_distrib]
      _ = (Fintype.card α : ℝ) + (∑ x : α, X x) * (Real.exp lam - 1) := by
            rw [Finset.sum_const, Finset.card_univ]
            rw [Finset.sum_mul]
            simp [nsmul_eq_mul]
  -- E[e^{λX}] = 1 + p(e^λ − 1)
  have hE : uniformExpectation (fun x => Real.exp (lam * X x)) = 1 + p * (Real.exp lam - 1) := by
    unfold uniformExpectation
    rw [hsum, hsumR]
    have hsumX : (∑ x : α, X x) = (Fintype.card α : ℝ) * p := sum_eq_card_mul_mean hN hmean
    rw [hsumX]
    field_simp [ne_of_gt (Nat.cast_pos.mpr hN)]
    ring
  -- 1 + p(e^λ−1) ≤ e^{p(e^λ−1)}（mathlib：add_one_le_exp）
  rw [hE]
  simpa [add_comm] using Real.add_one_le_exp (p * (Real.exp lam - 1))

/-! ## 引理 2：独立和的矩生成函数 = 各变量矩生成函数之积
（乘积空间 `Fin n → α` 上的计数期望分解：∏ᵢ∑ₓ = ∑_w∏ᵢ，`Finset.prod_univ_sum`）。 -/

theorem sum_mgf_factor {α : Type*} [Fintype α] (X : Fin n → α → ℝ) (lam : ℝ) :
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, X i (w i)))) =
      ∏ i : Fin n, uniformExpectation (fun x : α => Real.exp (lam * X i x)) := by
  have hfunc : (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, X i (w i))))
      = fun w : Fin n → α => ∏ i : Fin n, Real.exp (lam * X i (w i)) := by
    funext w
    calc
      Real.exp (lam * (∑ i : Fin n, X i (w i))) = Real.exp (∑ i : Fin n, lam * X i (w i)) := by
        rw [Finset.mul_sum]
      _ = ∏ i : Fin n, Real.exp (lam * X i (w i)) := Real.exp_sum _ _
  calc
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, X i (w i))))
        = (∑ w : Fin n → α, ∏ i : Fin n, Real.exp (lam * X i (w i))) /
            (Fintype.card (Fin n → α) : ℝ) := by
          unfold uniformExpectation
          rw [hfunc]
    _ = (∏ i : Fin n, ∑ x : α, Real.exp (lam * X i x)) / ((Fintype.card α : ℝ) ^ n) := by
          rw [Fintype.card_pi_const, Nat.cast_pow]
          congr 1
          rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset α))
            (f := fun i x => Real.exp (lam * X i x))]
          simp
    _ = ∏ i : Fin n, uniformExpectation (fun x : α => Real.exp (lam * X i x)) := by
          unfold uniformExpectation
          calc
            (∏ i : Fin n, ∑ x : α, Real.exp (lam * X i x)) / ((Fintype.card α : ℝ) ^ n)
                = (∏ i : Fin n, ∑ x : α, Real.exp (lam * X i x)) /
                    (∏ i : Fin n, (Fintype.card α : ℝ)) := by
                  congr 1
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ = ∏ i : Fin n, ((∑ x : α, Real.exp (lam * X i x)) / (Fintype.card α : ℝ)) := by
                  rw [Finset.prod_div_distrib]

/-! ## 引理 3：独立和的矩生成函数上界
S = Σᵢ Xᵢ（各坐标伯努利、E[Xᵢ] = pᵢ）⟹ E[e^{λS}] ≤ e^{(Σpᵢ)(e^λ−1)}。
证明：乘积分解（引理 2）+ 逐坐标界（引理 1）+ ∏e^{aᵢ} = e^{Σaᵢ}。 -/

theorem sum_mgf_le {α : Type*} [Fintype α] (X : Fin n → α → ℝ) (p : Fin n → ℝ) (lam : ℝ)
    (hN : 0 < Fintype.card α) (hmean : ∀ i, uniformExpectation (X i) = p i)
    (hval : ∀ i x, X i x = 0 ∨ X i x = 1) :
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, X i (w i)))) ≤
      Real.exp ((∑ i : Fin n, p i) * (Real.exp lam - 1)) := by
  rw [sum_mgf_factor X lam]
  calc
    ∏ i : Fin n, uniformExpectation (fun x : α => Real.exp (lam * X i x))
        ≤ ∏ i : Fin n, Real.exp (p i * (Real.exp lam - 1)) := by
          apply Finset.prod_le_prod
          · intro i hi
            unfold uniformExpectation
            exact div_nonneg (Finset.sum_nonneg (fun x hx => Real.exp_nonneg _)) (Nat.cast_nonneg _)
          · intro i hi
            exact bernoulli_mgf_bound (X := X i) (p := p i) (lam := lam) hN (hmean i) (hval i)
    _ = Real.exp ((∑ i : Fin n, p i) * (Real.exp lam - 1)) := by
          simpa [Finset.sum_mul] using
            (Real.exp_sum (s := Finset.univ) (f := fun i : Fin n => p i * (Real.exp lam - 1))).symm

/-! ## 引理 4：切尔诺夫桥（下尾方向）
P(S ≤ t) ≤ e^{λt}·E[e^{−λS}]（λ > 0）。证明：{S ≤ t} ⊆ {e^{−λt} ≤ e^{−λS}}
（exp 单调）+ 计数马尔可夫（f = e^{−λS}，阈值 e^{−λt}）。 -/

theorem markov_exp_tail_neg {α : Type*} [Fintype α] (S : α → ℝ) {t lam : ℝ} (hlam : 0 < lam) :
    uniformProb (Finset.univ.filter (fun w => S w ≤ t)) ≤
      Real.exp (lam * t) * uniformExpectation (fun w => Real.exp (-lam * S w)) := by
  have hset : Finset.univ.filter (fun w => S w ≤ t) ⊆
      Finset.univ.filter (fun w => Real.exp (-lam * t) ≤ Real.exp (-lam * S w)) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    have hle : -lam * t ≤ -lam * S w := by
      have h1 : 0 ≤ lam := le_of_lt hlam
      have h2 : 0 ≤ t - S w := sub_nonneg.mpr hw.2
      have h3 : 0 ≤ lam * (t - S w) := mul_nonneg h1 h2
      nlinarith
    exact ⟨Finset.mem_univ _, Real.exp_le_exp.mpr hle⟩
  have hmono : uniformProb (Finset.univ.filter (fun w => S w ≤ t)) ≤
      uniformProb (Finset.univ.filter (fun w => Real.exp (-lam * t) ≤ Real.exp (-lam * S w))) := by
    unfold uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hset) (Nat.cast_nonneg _)
  have hmarkov := markov_counting (f := fun w => Real.exp (-lam * S w)) (ε := Real.exp (-lam * t))
    (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
  calc
    uniformProb (Finset.univ.filter (fun w => S w ≤ t)) ≤
        uniformProb (Finset.univ.filter (fun w => Real.exp (-lam * t) ≤ Real.exp (-lam * S w))) := hmono
    _ ≤ (1 / Real.exp (-lam * t)) * uniformExpectation (fun w => Real.exp (-lam * S w)) := hmarkov
    _ = Real.exp (lam * t) * uniformExpectation (fun w => Real.exp (-lam * S w)) := by
      congr 1
      rw [one_div, ← Real.exp_neg (-lam * t)]
      congr 1
      ring

/-! ## 引理 5（分析核心，上尾）：Padé 型对数下界
ln(1+δ) ≥ 2δ/(2+δ)（δ ∈ [0,1]）。
证明：p(δ) = ln(1+δ) − 2δ/(2+δ)，p(0) = 0，p' = δ²/((1+δ)(2+δ)²) > 0 于 (0,1)，
`strictMonoOn_of_deriv_pos`（mathlib 均值定理：连续 + 内部导数正 ⟹ 严格递增）。 -/

lemma log_one_add_pade {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    2 * δ / (2 + δ) ≤ Real.log (1 + δ) := by
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - 2 * t / (2 + t)
  -- 连续性（[0,1] 上 1+t ≥ 1、2+t ≥ 2，log 与有理式均连续）
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Icc 0 1) := by
      refine (Real.continuousOn_log.comp (by fun_prop : ContinuousOn (fun t : ℝ => 1 + t) (Set.Icc 0 1)) ?_)
      intro t ht
      have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
      simp [Set.mem_compl_iff]
      linarith
    have hrat : ContinuousOn (fun t : ℝ => 2 * t / (2 + t)) (Set.Icc 0 1) := by
      refine ContinuousOn.div (by fun_prop : ContinuousOn (fun t : ℝ => 2 * t) (Set.Icc 0 1))
        (by fun_prop : ContinuousOn (fun t : ℝ => 2 + t) (Set.Icc 0 1)) ?_
      intro t ht
      have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
      linarith
    exact hlog.sub hrat
  -- 内部导数：p' = 1/(1+x) − 4/(2+x)² = x²/((1+x)(2+x)²) > 0
  have hpos : ∀ x ∈ interior (Set.Icc 0 1), 0 < deriv f x := by
    intro x hx
    have hxi : x ∈ Set.Ioo 0 1 := by simpa [interior_Icc] using hx
    have hx0 : 0 < x := (Set.mem_Ioo.mp hxi).1
    have hx1 : x < 1 := (Set.mem_Ioo.mp hxi).2
    have hd : deriv f x = 1 / (1 + x) - 4 / (2 + x) ^ 2 := by
      have harg : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
        simpa using ((hasDerivAt_id x).const_add (1 : ℝ))
      have hlog' : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
        -- mathlib 的 `HasDerivAt.log`：d/dt log(f t) = f' / f t（无需手写链式法则）
        have hl := harg.log (by linarith [hx0] : 1 + x ≠ 0)
        simpa using hl
      have hnum : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      have hden : HasDerivAt (fun t : ℝ => 2 + t) 1 x := by
        simpa using (hasDerivAt_id x).const_add (2 : ℝ)
      have hdiv := hnum.div hden (by linarith [hx0] : 2 + x ≠ 0)
      have hrat' : HasDerivAt (fun t : ℝ => 2 * t / (2 + t)) (4 / (2 + x) ^ 2) x := by
        convert hdiv using 1
        field_simp [show (2 + x : ℝ) ≠ 0 by linarith [hx0]]
        ring
      have hmain := hlog'.sub hrat'
      simpa [f] using hmain.deriv
    rw [hd]
    have hpos' : 0 < x ^ 2 / ((1 + x) * (2 + x) ^ 2) := by positivity
    rw [show 1 / (1 + x) - 4 / (2 + x) ^ 2 = x ^ 2 / ((1 + x) * (2 + x) ^ 2) by
      field_simp [show (1 + x : ℝ) ≠ 0 by linarith [hx0],
        show (2 + x : ℝ) ≠ 0 by linarith [hx0]]
      ring]
    exact hpos'
  -- f 在 [0,1] 严格递增，f(0) = 0 ⟹ f(δ) ≥ 0
  have hmono : StrictMonoOn f (Set.Icc 0 1) :=
    strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) (1 : ℝ)) hcont hpos
  by_cases hδ : δ = 0
  · subst hδ
    simp [f]
  · have hδp : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδ)
    have hlt : f 0 < f δ := hmono (by simp) ⟨hδ0, hδ1⟩ hδp
    have hf0 : f 0 = 0 := by simp [f]
    have hnonneg : 0 ≤ f δ := le_of_lt (by simpa [hf0] using hlt)
    unfold f at hnonneg
    linarith

/-! ## 引理 6（上尾对数不等式）：δ − (1+δ)·ln(1+δ) ≤ −δ²/3（δ ∈ [0,1]）
路线：δ − (1+δ)ln(1+δ) ≤ δ − (1+δ)·2δ/(2+δ) = −δ²/(2+δ) ≤ −δ²/3
（2+δ ≤ 3 ⟹ 1/(2+δ) ≥ 1/3）。**常数 1/3 为经典锐常数，非保守估计。** -/

lemma chernoff_log_upper {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ - (1 + δ) * Real.log (1 + δ) ≤ -(δ ^ 2 / 3) := by
  have hpade : 2 * δ / (2 + δ) ≤ Real.log (1 + δ) := log_one_add_pade hδ0 hδ1
  have h1p : 0 ≤ 1 + δ := by linarith [hδ0]
  calc
    δ - (1 + δ) * Real.log (1 + δ) ≤ δ - (1 + δ) * (2 * δ / (2 + δ)) := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left hpade h1p) δ
    _ = -(δ ^ 2 / (2 + δ)) := by
      field_simp [show (2 + δ : ℝ) ≠ 0 by linarith [hδ0]]
      ring
    _ ≤ -(δ ^ 2 / 3) := by
      have h2pd : 0 < 2 + δ := by linarith [hδ0]
      have hden : 2 + δ ≤ 3 := by linarith [hδ1]
      have hrecip : (3 : ℝ)⁻¹ ≤ (2 + δ)⁻¹ := by
        exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3) h2pd).mpr hden
      have hmain : δ ^ 2 / 3 ≤ δ ^ 2 / (2 + δ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hrecip (sq_nonneg δ)
      linarith

/-! ## 引理 7（分析核心，下尾）：反双曲型对数上界
ln v ≤ (v − 1/v)/2（v ≥ 1）。
证明：q(v) = (v−1/v)/2 − ln v，q(1) = 0，q' = (v−1)²/(2v²) > 0 于 (1,∞)，
`strictMonoOn_of_deriv_pos`。 -/

lemma log_le_half_sub_inv {v : ℝ} (hv1 : 1 ≤ v) :
    Real.log v ≤ (v - 1 / v) / 2 := by
  let q : ℝ → ℝ := fun w => (w - 1 / w) / 2 - Real.log w
  -- 连续性（[1,∞) 上 w ≥ 1 > 0）
  have hcont : ContinuousOn q (Set.Ici 1) := by
    have hrec : ContinuousOn (fun w : ℝ => 1 / w) (Set.Ici 1) := by
      refine ContinuousOn.div (by fun_prop : ContinuousOn (fun w : ℝ => (1 : ℝ)) (Set.Ici 1))
        (by fun_prop : ContinuousOn (fun w : ℝ => w) (Set.Ici 1)) ?_
      intro w hw
      have hw1 : 1 ≤ w := (Set.mem_Ici.mp hw)
      linarith
    have hpoly : ContinuousOn (fun w : ℝ => (w - 1 / w) / 2) (Set.Ici 1) := by
      exact ((by fun_prop : ContinuousOn (fun w : ℝ => w) (Set.Ici 1)).sub hrec).div_const (2 : ℝ)
    have hlogc : ContinuousOn (fun w : ℝ => Real.log w) (Set.Ici 1) := by
      refine (Real.continuousOn_log.comp (by fun_prop : ContinuousOn (fun w : ℝ => w) (Set.Ici 1)) ?_)
      intro w hw
      have hw1 : 1 ≤ w := (Set.mem_Ici.mp hw)
      simp [Set.mem_compl_iff]
      linarith
    exact hpoly.sub hlogc
  -- 内部导数：q' = (1 + 1/x²)/2 − 1/x = (x−1)²/(2x²) > 0
  have hpos : ∀ x ∈ interior (Set.Ici 1), 0 < deriv q x := by
    intro x hx
    have hx1 : 1 < x := by simpa [interior_Ici] using hx
    have hxne : x ≠ 0 := by linarith
    have hd : deriv q x = (x - 1) ^ 2 / (2 * x ^ 2) := by
      have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
      have hrec' : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
        simpa [one_div] using (hid.inv hxne)
      have hlin : HasDerivAt (fun t : ℝ => t - 1 / t) (1 + 1 / x ^ 2) x := by
        have hsub := hid.sub hrec'
        convert hsub using 1
        ring
      have hdiv2 : HasDerivAt (fun t : ℝ => (t - 1 / t) / 2) ((1 + 1 / x ^ 2) / 2) x :=
        hlin.div_const (2 : ℝ)
      have hlog : HasDerivAt Real.log (1 / x) x := by
        simpa [one_div] using (Real.hasDerivAt_log hxne)
      have hq := hdiv2.sub hlog
      have hq' : deriv q x = (1 + 1 / x ^ 2) / 2 - 1 / x := by
        unfold q
        exact hq.deriv
      rw [hq']
      field_simp [hxne]
      ring
    rw [hd]
    have hx1pos : 0 < x - 1 := by linarith
    have hsq : 0 < (x - 1) ^ 2 := pow_pos hx1pos 2
    have hden : 0 < 2 * x ^ 2 := by positivity
    exact div_pos hsq hden
  -- q 在 [1,∞) 严格递增，q(1) = 0 ⟹ q(v) ≥ 0
  have hmono : StrictMonoOn q (Set.Ici 1) :=
    strictMonoOn_of_deriv_pos (convex_Ici (1 : ℝ)) hcont hpos
  by_cases hv : v = 1
  · subst hv
    simp [q]
  · have hv1' : 1 < v := lt_of_le_of_ne hv1 (Ne.symm hv)
    have hlt : q 1 < q v := hmono (by simp) (Set.mem_Ici.mpr hv1) hv1'
    have hq1 : q 1 = 0 := by simp [q]
    have hnonneg : 0 ≤ q v := le_of_lt (by simpa [hq1] using hlt)
    unfold q at hnonneg
    linarith

/-! ## 引理 8（下尾对数不等式）：(1−δ)·ln(1/(1−δ)) − δ ≤ −δ²/2（δ ∈ [0,1)）
路线：代入 v = 1/(1−δ) 到引理 7：ln(1/(1−δ)) ≤ (1/(1−δ) − (1−δ))/2
⟹ (1−δ)·ln(1/(1−δ)) ≤ (1−(1−δ)²)/2 ⟹ 左边 − δ ≤ −δ²/2。
**常数 1/2 为经典锐常数，非保守估计。** -/

lemma chernoff_log_lower {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (1 - δ) * Real.log (1 / (1 - δ)) - δ ≤ -(δ ^ 2 / 2) := by
  have hpos1d : 0 < 1 - δ := by linarith [hδ1]
  have hv1 : 1 ≤ 1 / (1 - δ) := by
    rw [le_div_iff₀ hpos1d]
    linarith [hδ0]
  have hb := log_le_half_sub_inv hv1
  have hmul : (1 - δ) * Real.log (1 / (1 - δ)) ≤
      (1 - δ) * ((1 / (1 - δ) - 1 / (1 / (1 - δ))) / 2) :=
    mul_le_mul_of_nonneg_left hb (le_of_lt hpos1d)
  calc
    (1 - δ) * Real.log (1 / (1 - δ)) - δ
        ≤ (1 - δ) * ((1 / (1 - δ) - 1 / (1 / (1 - δ))) / 2) - δ := sub_le_sub_right hmul δ
    _ = (1 - δ) * ((1 / (1 - δ) - (1 - δ)) / 2) - δ := by
          simp [one_div_div]
    _ = (1 - (1 - δ) ^ 2) / 2 - δ := by
          field_simp [ne_of_gt hpos1d]
          ring
    _ = -(δ ^ 2 / 2) := by ring

/-! ## 定理 5（核心）：乘性切尔诺夫上尾界
n 个独立伯努利 Xᵢ（E[Xᵢ] = pᵢ、Xᵢ ∈ {0,1}），S = Σᵢ Xᵢ，μ = Σᵢ pᵢ > 0：
P(S ≥ (1+δ)·μ) ≤ e^{−δ²μ/3}（δ ∈ (0,1]）。
证明路线：切尔诺夫桥（`markov_exp_tail`，λ = ln(1+δ)）+ 矩生成上界（`sum_mgf_le`）
⟹ P ≤ e^{−λ(1+δ)μ + μ(e^λ−1)} = e^{μ(δ − (1+δ)ln(1+δ))} ≤ e^{−δ²μ/3}（引理 6）。 -/

theorem chernoff_upper_tail {α : Type*} [Fintype α] (X : Fin n → α → ℝ) (p : Fin n → ℝ)
    (hN : 0 < Fintype.card α) (hmean : ∀ i, uniformExpectation (X i) = p i)
    (hval : ∀ i x, X i x = 0 ∨ X i x = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hμpos : 0 < (∑ i : Fin n, p i)) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
      (1 + δ) * (∑ i : Fin n, p i) ≤ ∑ i : Fin n, X i (w i))) ≤
      Real.exp (-((∑ i : Fin n, p i) * δ ^ 2 / 3)) := by
  let μ : ℝ := ∑ i : Fin n, p i
  let S : (Fin n → α) → ℝ := fun w => ∑ i : Fin n, X i (w i)
  let lam : ℝ := Real.log (1 + δ)
  have h1pd : 0 < 1 + δ := by linarith [hδ0]
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.log_pos (by linarith [hδ0])
  -- E[e^{λS}] ≤ e^{μ(e^λ−1)}（引理 3）
  have hmgf : uniformExpectation (fun w : Fin n → α => Real.exp (lam * S w)) ≤
      Real.exp (μ * (Real.exp lam - 1)) := by
    simpa [S, μ] using sum_mgf_le X p lam hN hmean hval
  -- 切尔诺夫桥（上尾方向，RealHoeffding 的 markov_exp_tail）
  have hbridge := markov_exp_tail (S := S) (t := (1 + δ) * μ) (lam := lam) hlam
  have hmain : uniformProb (Finset.univ.filter (fun w : Fin n → α => (1 + δ) * μ ≤ S w)) ≤
      Real.exp (-(μ * δ ^ 2 / 3)) := by
    calc
      uniformProb (Finset.univ.filter (fun w : Fin n → α => (1 + δ) * μ ≤ S w))
          ≤ Real.exp (-lam * ((1 + δ) * μ)) * uniformExpectation (fun w => Real.exp (lam * S w)) := hbridge
      _ ≤ Real.exp (-lam * ((1 + δ) * μ)) * Real.exp (μ * (Real.exp lam - 1)) :=
            mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = Real.exp (μ * (δ - (1 + δ) * lam)) := by
            rw [← Real.exp_add]
            congr 1
            have he : Real.exp lam = 1 + δ := by
              dsimp [lam]
              exact Real.exp_log h1pd
            rw [he]
            ring
      _ ≤ Real.exp (-(μ * δ ^ 2 / 3)) := by
            have hμ0 : 0 ≤ μ := le_of_lt hμpos
            have hlogineq : δ - (1 + δ) * Real.log (1 + δ) ≤ -(δ ^ 2 / 3) :=
              chernoff_log_upper (le_of_lt hδ0) hδ1
            have hstep : μ * (δ - (1 + δ) * lam) ≤ μ * (-(δ ^ 2 / 3)) :=
              mul_le_mul_of_nonneg_left (by simpa [lam] using hlogineq) hμ0
            calc
              Real.exp (μ * (δ - (1 + δ) * lam)) ≤ Real.exp (μ * (-(δ ^ 2 / 3))) :=
                Real.exp_le_exp.mpr hstep
              _ = Real.exp (-(μ * δ ^ 2 / 3)) := by
                congr 1
                ring
  simpa [μ, S] using hmain

/-! ## 定理 6（加分）：乘性切尔诺夫下尾界
P(S ≤ (1−δ)·μ) ≤ e^{−δ²μ/2}（δ ∈ (0,1)）。
证明路线：切尔诺夫桥下尾方向（`markov_exp_tail_neg`，λ = ln(1/(1−δ))）
+ 矩生成上界（`sum_mgf_le` 取 λ ↦ −λ）⟹
P ≤ e^{λ(1−δ)μ + μ(e^{−λ}−1)} = e^{μ((1−δ)ln(1/(1−δ)) − δ)} ≤ e^{−δ²μ/2}（引理 8）。 -/

theorem chernoff_lower_tail {α : Type*} [Fintype α] (X : Fin n → α → ℝ) (p : Fin n → ℝ)
    (hN : 0 < Fintype.card α) (hmean : ∀ i, uniformExpectation (X i) = p i)
    (hval : ∀ i x, X i x = 0 ∨ X i x = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμpos : 0 < (∑ i : Fin n, p i)) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
      (∑ i : Fin n, X i (w i)) ≤ (1 - δ) * (∑ i : Fin n, p i))) ≤
      Real.exp (-((∑ i : Fin n, p i) * δ ^ 2 / 2)) := by
  let μ : ℝ := ∑ i : Fin n, p i
  let S : (Fin n → α) → ℝ := fun w => ∑ i : Fin n, X i (w i)
  let lam : ℝ := Real.log (1 / (1 - δ))
  have hpos1d : 0 < 1 - δ := by linarith [hδ1]
  have hlam : 0 < lam := by
    dsimp [lam]
    have hpos : 0 < 1 / (1 - δ) := by positivity
    rw [Real.log_pos_iff hpos]
    rw [lt_div_iff₀ hpos1d]
    linarith [hδ0]
  -- E[e^{−λS}] ≤ e^{μ(e^{−λ}−1)}（引理 3 取 lam ↦ −lam）
  have hmgf : uniformExpectation (fun w : Fin n → α => Real.exp (-lam * S w)) ≤
      Real.exp (μ * (Real.exp (-lam) - 1)) := by
    simpa [S, μ] using sum_mgf_le X p (-lam) hN hmean hval
  -- 切尔诺夫桥（下尾方向）
  have hbridge := markov_exp_tail_neg (S := S) (t := (1 - δ) * μ) (lam := lam) hlam
  have hmain : uniformProb (Finset.univ.filter (fun w : Fin n → α => S w ≤ (1 - δ) * μ)) ≤
      Real.exp (-(μ * δ ^ 2 / 2)) := by
    calc
      uniformProb (Finset.univ.filter (fun w : Fin n → α => S w ≤ (1 - δ) * μ))
          ≤ Real.exp (lam * ((1 - δ) * μ)) * uniformExpectation (fun w => Real.exp (-lam * S w)) := hbridge
      _ ≤ Real.exp (lam * ((1 - δ) * μ)) * Real.exp (μ * (Real.exp (-lam) - 1)) :=
            mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ = Real.exp (μ * ((1 - δ) * lam - δ)) := by
            rw [← Real.exp_add]
            congr 1
            have he : Real.exp (-lam) = 1 - δ := by
              dsimp [lam]
              rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / (1 - δ))]
              field_simp [ne_of_gt hpos1d]
            rw [he]
            ring
      _ ≤ Real.exp (-(μ * δ ^ 2 / 2)) := by
            have hμ0 : 0 ≤ μ := le_of_lt hμpos
            have hlogineq : (1 - δ) * Real.log (1 / (1 - δ)) - δ ≤ -(δ ^ 2 / 2) :=
              chernoff_log_lower (le_of_lt hδ0) hδ1
            have hstep : μ * ((1 - δ) * lam - δ) ≤ μ * (-(δ ^ 2 / 2)) :=
              mul_le_mul_of_nonneg_left (by simpa [lam] using hlogineq) hμ0
            calc
              Real.exp (μ * ((1 - δ) * lam - δ)) ≤ Real.exp (μ * (-(δ ^ 2 / 2))) :=
                Real.exp_le_exp.mpr hstep
              _ = Real.exp (-(μ * δ ^ 2 / 2)) := by
                congr 1
                ring
  simpa [μ, S] using hmain

/-! ## 定理 7（加分）：双边乘性切尔诺夫界
P(|S − μ| ≥ δ·μ) ≤ 2·e^{−δ²μ/3}（δ ∈ (0,1)）。
证明：{|S−μ| ≥ δμ} ⊆ {S ≥ (1+δ)μ} ∪ {S ≤ (1−δ)μ}（|a| ≥ t 且 t ≥ 0 ⟹ a ≥ t 或 a ≤ −t）
+ 上尾界（定理 5，常数 1/3）+ 下尾界（定理 6，常数 1/2，e^{−δ²μ/2} ≤ e^{−δ²μ/3}）+ 并集界。 -/

theorem chernoff_two_sided {α : Type*} [Fintype α] [DecidableEq α]
    (X : Fin n → α → ℝ) (p : Fin n → ℝ)
    (hN : 0 < Fintype.card α) (hmean : ∀ i, uniformExpectation (X i) = p i)
    (hval : ∀ i x, X i x = 0 ∨ X i x = 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμpos : 0 < (∑ i : Fin n, p i)) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
      δ * (∑ i : Fin n, p i) ≤ |(∑ i : Fin n, X i (w i)) - (∑ i : Fin n, p i)|)) ≤
      2 * Real.exp (-((∑ i : Fin n, p i) * δ ^ 2 / 3)) := by
  let μ : ℝ := ∑ i : Fin n, p i
  let S : (Fin n → α) → ℝ := fun w => ∑ i : Fin n, X i (w i)
  let A : Finset (Fin n → α) := Finset.univ.filter (fun w : Fin n → α => δ * μ ≤ |S w - μ|)
  let B : Finset (Fin n → α) := Finset.univ.filter (fun w : Fin n → α => (1 + δ) * μ ≤ S w)
  let C : Finset (Fin n → α) := Finset.univ.filter (fun w : Fin n → α => S w ≤ (1 - δ) * μ)
  -- {δμ ≤ |S−μ|} ⊆ {S ≥ (1+δ)μ} ∪ {S ≤ (1−δ)μ}
  have hsub : A ⊆ B ∪ C := by
    intro w hw
    have hA : δ * μ ≤ |S w - μ| := (Finset.mem_filter.mp hw).2
    let a := S w - μ
    have hδμ : 0 ≤ δ * μ := mul_nonneg (le_of_lt hδ0) (le_of_lt hμpos)
    have hcases : δ * μ ≤ a ∨ a ≤ -(δ * μ) := by
      by_cases h1 : δ * μ ≤ a
      · exact Or.inl h1
      · right
        by_cases h2 : 0 ≤ a
        · have hAbs : |a| = a := abs_of_nonneg h2
          exact False.elim (h1 (by simpa [a, hAbs] using hA))
        · have hAbs : |a| = -a := abs_of_neg (lt_of_not_ge h2)
          have htna : δ * μ ≤ -a := by simpa [a, hAbs] using hA
          exact neg_le_neg_iff.mp (by simpa using htna)
    rcases hcases with hl | hr
    · rw [Finset.mem_union]
      left
      dsimp [B]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      dsimp [a] at hl
      linarith [hl]
    · rw [Finset.mem_union]
      right
      dsimp [C]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      dsimp [a] at hr
      linarith [hr]
  -- 并集界 + 两个尾界
  have hmono : uniformProb A ≤ uniformProb (B ∪ C) := by
    unfold uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (Nat.cast_nonneg _)
  have hsubadd : uniformProb (B ∪ C) ≤ uniformProb B + uniformProb C := by
    unfold uniformProb
    calc
      (B ∪ C).card / (Fintype.card (Fin n → α) : ℝ) ≤
          (B.card + C.card) / (Fintype.card (Fin n → α) : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast (Finset.card_union_le B C)) (Nat.cast_nonneg _)
      _ = B.card / (Fintype.card (Fin n → α) : ℝ) + C.card / (Fintype.card (Fin n → α) : ℝ) := by ring
  have hB : uniformProb B ≤ Real.exp (-(μ * δ ^ 2 / 3)) := by
    simpa [B, μ, S] using chernoff_upper_tail X p hN hmean hval hδ0 (le_of_lt hδ1) hμpos
  have hC : uniformProb C ≤ Real.exp (-(μ * δ ^ 2 / 2)) := by
    simpa [C, μ, S] using chernoff_lower_tail X p hN hmean hval hδ0 hδ1 hμpos
  have hC' : uniformProb C ≤ Real.exp (-(μ * δ ^ 2 / 3)) := by
    have hμδ2 : 0 ≤ μ * δ ^ 2 := mul_nonneg (le_of_lt hμpos) (sq_nonneg δ)
    exact hC.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hmain : uniformProb A ≤ 2 * Real.exp (-(μ * δ ^ 2 / 3)) := by
    calc
      uniformProb A ≤ uniformProb (B ∪ C) := hmono
      _ ≤ uniformProb B + uniformProb C := hsubadd
      _ ≤ Real.exp (-(μ * δ ^ 2 / 3)) + Real.exp (-(μ * δ ^ 2 / 3)) := add_le_add hB hC'
      _ = 2 * Real.exp (-(μ * δ ^ 2 / 3)) := by ring
  simpa [A, μ, S] using hmain

/-! ## 注：与 Hoeffding / SamplingBoost 的衔接
RealHoeffding 给出**加性** Hoeffding 界 P(X̄ − μ ≥ t) ≤ e^{−nt²/8}；本文件给出
**乘性** Chernoff 界 P(S ≥ (1+δ)μ) ≤ e^{−δ²μ/3}（μ = Σpᵢ 为和自身的期望）。
两者共享完全相同的证明骨架：切尔诺夫桥（`markov_exp_tail`）+ 乘积空间矩生成分解
（`Finset.prod_univ_sum`）+ 每变量矩生成上界；区别仅在 MGF 上界的来源
（Hoeffding：exp 凸性弦上界；Chernoff：伯努利精确期望 1 + p(e^λ−1) ≤ e^{p(e^λ−1)}）
与偏差度量（加性 t vs 乘性 δμ）。配合 RealSamplingBoost 的 `boost_confidence`，
指数型单轮界可放大为多轮采样验证的指数级置信提升。 -/

end Lattice
