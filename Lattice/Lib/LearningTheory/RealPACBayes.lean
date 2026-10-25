import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: PAC-Bayes 界（有限假设集版）—— 变测度法（change of measure）

方向：`RealRademacher` / `RealUnionBound` 给出的泛化界都是**一致收敛**型
（对假设类中**每个**假设同时成立，容量代价是 `log |F|`）。PAC-Bayes 给出
**数据相关**的界：把先验 `P`、后验 `Q` 都放在有限假设集 `Fin k` 上，
容量代价是 `KL(Q‖P)`（`RealKL.kl`）而不是 `log |F|`，且允许泄漏
`log(1/δ)` 的最坏情形因子。本文件给出有限支撑版的完整证明。

**设定**：假设集 `Fin k`（k > 0）、样本空间 `Z` 有限（非空）、样本数 `n > 0`、
数据分布取均匀分布、损失 `loss : Fin k → Z → ℝ` 取值在 `[0,1]`。
样本 `w : Fin n → Z` 在乘积空间 `Fin n → Z` 上均匀分布。
`pacBayesRisk loss h` 是风险 `E_z[loss h z]`，`pacBayesEmpRisk loss h w`
是经验风险 `(1/n)Σᵢ loss h (w i)`。

**定理链**：
1. `pacBayes_mgf_single`：零均值、`|X| ≤ 1` 的有界变量，n 个独立副本的 MGF
   `E_w[e^{μΣᵢX(wᵢ)}] ≤ exp(n μ²/2)`（`RealHoeffding.hoeffding_lemma` 的乘积分解）。
   **这是锐利的 Hoeffding 引理**（常数 1/2），而不是
   `RealHoeffding.hoeffding_lemma_bounded` 的保守常数 2。
2. `pacBayes_mgf_hypothesis`：损失取值 `[0,1]` 时，对**每个**假设 `h`，
   `E_w[e^{λ(R(h) − R̂(h,w))}] ≤ exp(λ²/(2n))`。
   证明：`X(z) = R(h) − loss h z` 满足 `|X| ≤ 1`、`ΣX = 0`，取 `μ = λ/n`。
3. `pacBayes_prior_moment_mgf`：先验加权指数矩
   `E_w[Σ_h P_h e^{λ(R(h) − R̂(h,w))}] ≤ exp(λ²/(2n))`（用 `ΣP_h = 1`）。
4. `pacBayes_change_of_measure`（**变测度不等式 / Gibbs 变分式**）：
   `Σ_h Q_h Z_h ≤ KL(Q‖P) + log(Σ_h P_h e^{Z_h})`。
   证明：加权 AM-GM（`Real.geom_mean_le_arith_mean_weighted`）作用于
   `a_h = P_h e^{Z_h}/Q_h`，再取 log：
   `log(∏ a_h^{Q_h}) = Σ Q_h log a_h ≤ log(Σ Q_h a_h) = log(Σ P_h e^{Z_h})`，
   而 `Σ Q_h log a_h = Σ Q_h Z_h − KL(Q‖P)`。
5. `pacBayes_bound`（**主定理**）：`0 < δ`、`λ > 0` 时，
   「`Σ_h Q_h R(h) > Σ_h Q_h R̂(h,w) + (KL(Q‖P) + log(1/δ) + λ²/(2n))/λ`」
   这一**违背事件**的概率 ≤ δ（即上式以概率 ≥ 1 − δ 成立）。
   证明：马尔可夫（`RealHoeffding.markov_counting`）作用于先验加权指数矩
   （定理 3），再用定理 4 把违背事件包含进马尔可夫事件。
6. `pacBayes_risk_bound_of_exponent`：把指数形式的界重排为风险形式的界
   （纯 `linarith`，除以 `lam > 0`）。

**诚实标注**：本文件是**有限支撑**（`Fin k`）的 PAC-Bayes；连续先验/后验、
可数支撑、以及 KL 的最优 `λ` 选择（`λ* = sqrt(2n(KL+log(1/δ)))`，给出
`sqrt(2(KL+log(1/δ))/n)` 型界）**未证/未做**——本文件给出对任意 `λ > 0` 的界，
最优 `λ` 的代入是初等代数但不在本文件展开。`Real.log` 是全函数，
但本文件所有 log 都在正数处使用。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、风险与经验风险 -/

/-- 风险：假设 `h` 在均匀数据分布下的期望损失 `E_z[loss h z]`。 -/
noncomputable def pacBayesRisk {Z : Type*} [Fintype Z] {k : ℕ} (loss : Fin k → Z → ℝ)
    (h : Fin k) : ℝ :=
  uniformExpectation (loss h)

/-- 经验风险：`(1/n)·Σᵢ loss h (w i)`（示例 `w : Fin n → Z`）。 -/
noncomputable def pacBayesEmpRisk {Z : Type*} {k n : ℕ} (loss : Fin k → Z → ℝ)
    (h : Fin k) (w : Fin n → Z) : ℝ :=
  (∑ i : Fin n, loss h (w i)) / (n : ℝ)

/-- 先验加权指数矩：`Σ_h P_h · e^{λ(R(h) − R̂(h,w))}`。 -/
noncomputable def pacBayesPriorMoment {Z : Type*} [Fintype Z] {k n : ℕ} (loss : Fin k → Z → ℝ)
    (P : Fin k → ℝ) (lam : ℝ) (w : Fin n → Z) : ℝ :=
  ∑ h : Fin k, P h * Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w))

/-- 后验风险：`E_{h~Q}[R(h)] = Σ_h Q_h R(h)`。 -/
noncomputable def pacBayesPosteriorRisk {Z : Type*} [Fintype Z] {k : ℕ} (loss : Fin k → Z → ℝ)
    (Q : Fin k → ℝ) : ℝ :=
  ∑ h : Fin k, Q h * pacBayesRisk loss h

/-- 后验经验风险：`Σ_h Q_h R̂(h,w)`。 -/
noncomputable def pacBayesPosteriorEmpRisk {Z : Type*} {k n : ℕ} (loss : Fin k → Z → ℝ)
    (Q : Fin k → ℝ) (w : Fin n → Z) : ℝ :=
  ∑ h : Fin k, Q h * pacBayesEmpRisk loss h w

/-! ## 二、单假设的 MGF 界（锐利 Hoeffding 常数 1/2） -/

/-- **n 个独立副本的锐利 Hoeffding MGF 界**：零均值、`|X| ≤ 1`、样本空间非空 ⟹
`E_w[e^{μ·ΣᵢX(wᵢ)}] ≤ exp(n·μ²/2)`。证明：乘积分解
（`Finset.prod_univ_sum`）把乘积空间的期望拆为单坐标期望之积，
每个因子用 `RealHoeffding.hoeffding_lemma`（常数 `μ²/2`）控制。
这是 `RealHoeffding.hoeffding_tail_bounded` 的「锐利版」——那里因
`|Y| ≤ 2`（均值平移）用了保守常数 2。 -/
theorem pacBayes_mgf_single {Z : Type*} [Fintype Z] {X : Z → ℝ} (n : ℕ)
    (hN : 0 < Fintype.card Z) (hzero : (∑ z : Z, X z) = 0) (hb : ∀ z : Z, |X z| ≤ 1)
    (mu : ℝ) :
    uniformExpectation (fun w : Fin n → Z => Real.exp (mu * ∑ i : Fin n, X (w i))) ≤
      Real.exp ((n : ℝ) * mu ^ 2 / 2) := by
  have hfunc : (fun w : Fin n → Z => Real.exp (mu * (∑ i : Fin n, X (w i))))
      = fun w : Fin n → Z => ∏ i : Fin n, Real.exp (mu * X (w i)) := by
    funext w
    rw [Finset.mul_sum, Real.exp_sum]
  calc
    uniformExpectation (fun w : Fin n → Z => Real.exp (mu * ∑ i : Fin n, X (w i)))
        = (∏ i : Fin n, ∑ z : Z, Real.exp (mu * X z)) / ((Fintype.card Z : ℝ) ^ n) := by
          unfold uniformExpectation
          rw [hfunc, Fintype.card_pi_const, Nat.cast_pow]
          congr 1
          rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset Z))
            (f := fun i z => Real.exp (mu * X z))]
          simp
    _ = ∏ i : Fin n, uniformExpectation (fun z => Real.exp (mu * X z)) := by
          unfold uniformExpectation
          rw [Finset.prod_div_distrib]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ _i : Fin n, Real.exp (mu ^ 2 / 2) := by
          apply Finset.prod_le_prod
          · intro i _
            unfold uniformExpectation
            exact div_nonneg (Finset.sum_nonneg (fun z _ => Real.exp_nonneg _)) (Nat.cast_nonneg _)
          · intro i _
            exact hoeffding_lemma hN hzero hb
    _ = Real.exp ((n : ℝ) * mu ^ 2 / 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1
          ring

/-- **单假设的 PAC-Bayes MGF 界**：损失取值 `[0,1]`、`n > 0` 时，
`E_w[e^{λ(R(h) − R̂(h,w))}] ≤ exp(λ²/(2n))`。
证明：`X(z) = R(h) − loss h z`，`ΣX = 0`（因为 `R(h)` 是均值）、`|X| ≤ 1`
（`R(h), loss h z ∈ [0,1]`），对 `μ = λ/n` 用定理 `pacBayes_mgf_single`。 -/
theorem pacBayes_mgf_hypothesis {Z : Type*} [Fintype Z] (k n : ℕ)
    (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (loss : Fin k → Z → ℝ) (h01 : ∀ h z, 0 ≤ loss h z ∧ loss h z ≤ 1)
    (h : Fin k) (lam : ℝ) :
    uniformExpectation (fun w : Fin n → Z =>
        Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w))) ≤
      Real.exp (lam ^ 2 / (2 * (n : ℝ))) := by
  let X : Z → ℝ := fun z => pacBayesRisk loss h - loss h z
  have hmean : uniformExpectation (loss h) = pacBayesRisk loss h := rfl
  have hR01 : 0 ≤ pacBayesRisk loss h ∧ pacBayesRisk loss h ≤ 1 := by
    constructor
    · unfold pacBayesRisk uniformExpectation
      exact div_nonneg (Finset.sum_nonneg (fun z _ => (h01 h z).1)) (Nat.cast_nonneg _)
    · unfold pacBayesRisk uniformExpectation
      rw [div_le_one (Nat.cast_pos.mpr hN)]
      calc (∑ z : Z, loss h z) ≤ ∑ _z : Z, (1 : ℝ) :=
            Finset.sum_le_sum (fun z _ => (h01 h z).2)
        _ = (Fintype.card Z : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hXb : ∀ z : Z, |X z| ≤ 1 := by
    intro z
    have hz := h01 h z
    rw [abs_le]
    constructor
    · show -1 ≤ pacBayesRisk loss h - loss h z
      linarith [hR01.1, hz.2]
    · show pacBayesRisk loss h - loss h z ≤ 1
      linarith [hR01.2, hz.1]
  have hXzero : (∑ z : Z, X z) = 0 := by
    have hcard := sum_eq_card_mul_mean hN hmean
    show (∑ z : Z, (pacBayesRisk loss h - loss h z)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    ring
  have hmgf := pacBayes_mgf_single (X := X) n hN hXzero hXb (lam / (n : ℝ))
  have hfun : (fun w : Fin n → Z =>
        Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)))
      = fun w : Fin n → Z => Real.exp ((lam / (n : ℝ)) * ∑ i : Fin n, X (w i)) := by
    funext w
    congr 1
    show lam * (pacBayesRisk loss h - (∑ i : Fin n, loss h (w i)) / (n : ℝ))
        = (lam / (n : ℝ)) * ∑ i : Fin n, (pacBayesRisk loss h - loss h (w i))
    have hsum : (∑ i : Fin n, (pacBayesRisk loss h - loss h (w i)))
        = (n : ℝ) * pacBayesRisk loss h - ∑ i : Fin n, loss h (w i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [hsum, div_eq_mul_inv, div_eq_mul_inv]
    field_simp
    exact Or.inl (mul_comm _ _)
  have hexp : (n : ℝ) * (lam / (n : ℝ)) ^ 2 / 2 = lam ^ 2 / (2 * (n : ℝ)) := by
    field_simp
    ring
  calc
    uniformExpectation (fun w : Fin n → Z =>
        Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)))
        = uniformExpectation (fun w : Fin n → Z =>
            Real.exp ((lam / (n : ℝ)) * ∑ i : Fin n, X (w i))) := by rw [hfun]
    _ ≤ Real.exp ((n : ℝ) * (lam / (n : ℝ)) ^ 2 / 2) := hmgf
    _ = Real.exp (lam ^ 2 / (2 * (n : ℝ))) := by rw [hexp]

/-! ## 三、先验加权指数矩 -/

/-- **先验加权指数矩的界**：`E_w[Σ_h P_h e^{λ(R(h) − R̂(h,w))}] ≤ exp(λ²/(2n))`。
证明：交换有限和（`Finset.sum_comm`）+ 每个假设的 MGF 界 + `Σ_h P_h = 1`。 -/
theorem pacBayes_prior_moment_mgf {Z : Type*} [Fintype Z] (k n : ℕ)
    (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (P : Fin k → ℝ) (loss : Fin k → Z → ℝ)
    (hP : ∀ h, 0 < P h) (hPsum : ∑ h, P h = 1) (h01 : ∀ h z, 0 ≤ loss h z ∧ loss h z ≤ 1)
    (lam : ℝ) :
    uniformExpectation (fun w : Fin n → Z => pacBayesPriorMoment loss P lam w) ≤
      Real.exp (lam ^ 2 / (2 * (n : ℝ))) := by
  have hpoint : ∀ h : Fin k,
      uniformExpectation (fun w : Fin n → Z =>
          Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w))) ≤
        Real.exp (lam ^ 2 / (2 * (n : ℝ))) :=
    fun h => pacBayes_mgf_hypothesis k n hN hn loss h01 h lam
  have hstep : uniformExpectation (fun w : Fin n → Z => pacBayesPriorMoment loss P lam w)
      = ∑ h : Fin k, P h * uniformExpectation (fun w : Fin n → Z =>
          Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w))) := by
    unfold pacBayesPriorMoment uniformExpectation
    rw [Finset.sum_comm]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro h _
    have hmul : P h * (∑ w : Fin n → Z,
        Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)))
        = ∑ w : Fin n → Z,
          P h * Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)) := by
      rw [Finset.mul_sum]
    rw [← hmul, mul_div_assoc]
  rw [hstep]
  calc ∑ h : Fin k, P h * uniformExpectation (fun w : Fin n → Z =>
          Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)))
      ≤ ∑ h : Fin k, P h * Real.exp (lam ^ 2 / (2 * (n : ℝ))) :=
        Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hpoint h) (le_of_lt (hP h)))
    _ = Real.exp (lam ^ 2 / (2 * (n : ℝ))) := by
        rw [← Finset.sum_mul, hPsum, one_mul]

/-! ## 四、变测度不等式（Gibbs 变分式） -/

/-- **变测度不等式**：对 `P, Q > 0`、`Σ_h Q_h = 1`、`k > 0`，
`Σ_h Q_h Z_h ≤ KL(Q‖P) + log(Σ_h P_h e^{Z_h})`，
其中 `KL(Q‖P) = kl Q P`（`RealKL.kl`，CE − H 形式）。

证明：令 `a_h = P_h e^{Z_h}/Q_h > 0`。加权 AM-GM
（`Real.geom_mean_le_arith_mean_weighted`，权重 `Q_h`、和为 1）给出
`∏_h a_h^{Q_h} ≤ Σ_h Q_h a_h = Σ_h P_h e^{Z_h}`。两边取 log：
`Σ_h Q_h log a_h = log(∏ a_h^{Q_h}) ≤ log(Σ_h P_h e^{Z_h})`，
而 `log a_h = Z_h + log P_h − log Q_h`，故
`Σ_h Q_h log a_h = Σ_h Q_h Z_h − KL(Q‖P)`。 -/
theorem pacBayes_change_of_measure {k : ℕ} (hk : 0 < k) (P Q : Fin k → ℝ) (Z : Fin k → ℝ)
    (hP : ∀ h, 0 < P h) (hQ : ∀ h, 0 < Q h) (hQsum : ∑ h, Q h = 1) :
    (∑ h, Q h * Z h) ≤ kl Q P + Real.log (∑ h, P h * Real.exp (Z h)) := by
  set a : Fin k → ℝ := fun h => P h * Real.exp (Z h) / Q h with ha
  have hapos : ∀ h, 0 < a h := fun h =>
    div_pos (mul_pos (hP h) (Real.exp_pos (Z h))) (hQ h)
  have hamgm : (∏ h ∈ Finset.univ, a h ^ (Q h)) ≤ ∑ h ∈ Finset.univ, Q h * a h :=
    Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (w := Q) (z := a)
      (fun h _ => le_of_lt (hQ h)) hQsum (fun h _ => le_of_lt (hapos h))
  have harith : (∑ h ∈ Finset.univ, Q h * a h) = ∑ h, P h * Real.exp (Z h) := by
    apply Finset.sum_congr rfl
    intro h _
    simp only [ha]
    have hq : Q h ≠ 0 := ne_of_gt (hQ h)
    field_simp
  have hlog : ∀ h, Real.log (a h) = Z h + Real.log (P h) - Real.log (Q h) := by
    intro h
    simp only [ha]
    rw [Real.log_div (ne_of_gt (mul_pos (hP h) (Real.exp_pos (Z h)))) (ne_of_gt (hQ h)),
        Real.log_mul (ne_of_gt (hP h)) (Real.exp_ne_zero (Z h)), Real.log_exp]
    ring
  have hgeom : Real.log (∏ h ∈ Finset.univ, a h ^ (Q h)) = ∑ h, Q h * Real.log (a h) := by
    rw [Real.log_prod Finset.univ (fun h => a h ^ (Q h))
      (fun h _ => ne_of_gt (Real.rpow_pos_of_pos (hapos h) (Q h)))]
    apply Finset.sum_congr rfl
    intro h _
    rw [Real.log_rpow (hapos h)]
  have hgeom_eq : (∑ h, Q h * Real.log (a h)) = ∑ h, Q h * Z h - kl Q P := by
    have hstep : (∑ h, Q h * Real.log (a h))
        = ∑ h, Q h * (Z h + Real.log (P h) - Real.log (Q h)) :=
      Finset.sum_congr rfl (fun h _ => by rw [hlog h])
    rw [hstep, kl_as_sum_log_sub_log]
    simp only [mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hlog_le : (∑ h, Q h * Real.log (a h)) ≤ Real.log (∑ h, P h * Real.exp (Z h)) := by
    have hpos_prod : 0 < ∏ h ∈ Finset.univ, a h ^ (Q h) :=
      Finset.prod_pos (fun h _ => Real.rpow_pos_of_pos (hapos h) (Q h))
    have hle := Real.log_le_log hpos_prod hamgm
    rwa [hgeom, harith] at hle
  linarith [hgeom_eq ▸ hlog_le]

/-! ## 五、PAC-Bayes 主定理 -/

/-- **PAC-Bayes 违背事件概率界（主定理）**：有限假设集 `Fin k`、样本空间 `Z` 有限非空、
`n > 0`、先验 `P > 0` 且 `ΣP = 1`、后验 `Q > 0` 且 `ΣQ = 1`、损失取值 `[0,1]`、
`δ > 0`、`λ > 0`。其中 `hk : 0 < k` 承重（假设集非空）：证明需为 `Fin k` 取非空
见证 `⟨0, hk⟩` 以保证 `G(w) = Σ_h P_h e^{λ(R(h) − R̂(h,w))} > 0`，故 `k = 0` 不在覆盖范围内。
则「后验风险超过 后验经验风险 +
`(KL(Q‖P) + log(1/δ) + λ²/(2n))/λ`」这一**违背事件**的概率 ≤ δ ——
即 PAC-Bayes 界以置信度 `≥ 1 − δ` 成立。

证明：先验加权指数矩 `G(w) = Σ_h P_h e^{λ(R(h) − R̂(h,w))}` 满足
`E_w[G] ≤ exp(λ²/(2n))`（定理 `pacBayes_prior_moment_mgf`）；
马尔可夫（`RealHoeffding.markov_counting`）给出
`P(eps ≤ G) ≤ δ`，其中 `eps = (1/δ)·e^{λ²/(2n)}`。变测度不等式
（定理 `pacBayes_change_of_measure`）对 `Z_h = λ(R(h) − R̂(h,w))` 给出
`λ(Σ_h Q_h R(h) − Σ_h Q_h R̂(h,w)) ≤ KL(Q‖P) + log G(w)`，
故违背事件 ⊆ `{eps ≤ G}`，概率 ≤ δ。 -/
theorem pacBayes_bound {Z : Type*} [Fintype Z] [DecidableEq Z] (k n : ℕ)
    (hk : 0 < k) (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ)
    (hP : ∀ h, 0 < P h) (hPsum : ∑ h, P h = 1)
    (hQ : ∀ h, 0 < Q h) (hQsum : ∑ h, Q h = 1)
    (h01 : ∀ h z, 0 ≤ loss h z ∧ loss h z ≤ 1)
    {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Z =>
        pacBayesPosteriorRisk loss Q >
          pacBayesPosteriorEmpRisk loss Q w +
            (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam)) ≤ δ := by
  set G : (Fin n → Z) → ℝ := fun w =>
    ∑ h : Fin k, P h * Real.exp (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)) with hG
  set eps : ℝ := (1 / δ) * Real.exp (lam ^ 2 / (2 * (n : ℝ))) with heps
  have hGnonneg : ∀ w, 0 ≤ G w :=
    fun w => Finset.sum_nonneg (fun h _ => mul_nonneg (le_of_lt (hP h)) (Real.exp_nonneg _))
  have hGpos : ∀ w, 0 < G w := by
    intro w
    exact Finset.sum_pos (fun h _ => mul_pos (hP h) (Real.exp_pos _))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hE : uniformExpectation G ≤ Real.exp (lam ^ 2 / (2 * (n : ℝ))) := by
    have h := pacBayes_prior_moment_mgf k n hN hn P loss hP hPsum h01 lam
    simpa [hG, pacBayesPriorMoment] using h
  have hepspos : 0 < eps := by
    rw [heps]
    exact mul_pos (div_pos one_pos hδ) (Real.exp_pos _)
  have hmarkov : uniformProb (Finset.univ.filter (fun w : Fin n → Z => eps ≤ G w)) ≤ δ := by
    calc uniformProb (Finset.univ.filter (fun w : Fin n → Z => eps ≤ G w))
        ≤ (1 / eps) * uniformExpectation G := markov_counting hepspos hGnonneg
      _ ≤ (1 / eps) * Real.exp (lam ^ 2 / (2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hE (le_of_lt (one_div_pos.mpr hepspos))
      _ = δ := by
            rw [heps]
            field_simp
  -- 违背事件 ⊆ 马尔可夫事件
  have hsub : Finset.univ.filter (fun w : Fin n → Z =>
        pacBayesPosteriorRisk loss Q >
          pacBayesPosteriorEmpRisk loss Q w +
            (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam)
      ⊆ Finset.univ.filter (fun w : Fin n → Z => eps ≤ G w) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have hcm : (∑ h : Fin k, Q h * (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)))
        ≤ kl Q P + Real.log (G w) := by
      have h := pacBayes_change_of_measure hk P Q
        (fun h => lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)) hP hQ hQsum
      simpa [hG, pacBayesPriorMoment] using h
    have h1 : (∑ h : Fin k, Q h * (lam * (pacBayesRisk loss h - pacBayesEmpRisk loss h w)))
        = lam * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w) := by
      unfold pacBayesPosteriorRisk pacBayesPosteriorEmpRisk
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro h _
      ring
    have hT : kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))
        < (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w) * lam := by
      have hkey : (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam
          < pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w := by
        linarith [hw]
      exact (div_lt_iff₀ hlam).mp hkey
    have hloglt : Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ)) < Real.log (G w) := by
      rw [h1] at hcm
      linarith [hcm, hT]
    have he : eps < G w := by
      have h := Real.exp_lt_exp.mpr hloglt
      rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < 1 / δ),
        Real.exp_log (hGpos w)] at h
      simpa [heps] using h
    exact le_of_lt he
  exact le_trans (by
    unfold uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg _)) hmarkov

/-- **指数形式 ⟹ 风险形式**：若
`lam·(R_Q − R̂_Q(w)) ≤ KL(Q‖P) + log(1/δ) + λ²/(2n)`，
则风险形式的 PAC-Bayes 界成立。纯线性重排（除以 `lam > 0`）。 -/
theorem pacBayes_risk_bound_of_exponent {Z : Type*} [Fintype Z] {k n : ℕ}
    (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ) (w : Fin n → Z) {δ lam : ℝ}
    (hlam : 0 < lam)
    (h : lam * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w) ≤
      kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) :
    pacBayesPosteriorRisk loss Q ≤
      pacBayesPosteriorEmpRisk loss Q w +
        (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam := by
  have h2 : pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w
      ≤ (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam := by
    rw [le_div_iff₀ hlam]
    linarith [h]
  linarith

/-! ## 六、注：与 RealKL / RealHoeffding / RealUnionBound 的衔接

· `kl`（RealKL）提供 `KL(Q‖P) = CE − H` 与非负性 `kl_nonneg`；本文件的
  变测度不等式（定理 `pacBayes_change_of_measure`）是 `kl` 在泛化界中的**用法**——
  容量代价是 `KL(Q‖P)` 而非一致收敛型的 `log |F|`（后者见 `RealUnionBound`，
  本文件未 import、未引用其任何声明，该对比仅为语义对照）。
· `RealHoeffding.hoeffding_lemma`（锐利常数 `λ²/2`）通过
  `pacBayes_mgf_single` 的乘积分解给出 `exp(λ²/(2n))`，这正是 PAC-Bayes
  界主项 `sqrt(2(KL+log(1/δ))/n)` 的来源；若改用保守常数（如
  `RealBernstein` 的 `e^{−t²/(4nV)}`）则只能得到常数更差的界。
· **未做（诚实标注）**：连续/可数先验后验、最优 `λ` 的显式代入、
  以及 `RealGeneralizationBound` 中把本定理接入统一泛化界接口。
-/

end Lattice
