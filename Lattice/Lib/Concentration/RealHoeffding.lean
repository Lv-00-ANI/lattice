import Mathlib
import Lattice.Lib.LearningTheory.RealSamplingBoost
/-!
# LATTICE: Hoeffding 不等式 —— 有界独立随机变量之和的指数型集中界

方向（§5 验证行「Hoeffding」）：RealRandomVerify 的马尔可夫/切比雪夫界只给出
多项式型尾界（μ{f ≥ ε} ≤ ∫f/ε）；本文件把随机化验证的概率保证升级为
**指数型尾界**：n 个有界（|X_i| ≤ 1）独立随机变量的样本均值 X̄ 偏离期望 μ
超过 t 的概率按 e^{−c·n·t²} 指数衰减。

**设定（有限计数概率空间，衔接 RealSamplingBoost）**：样本空间 α 有限
（Fintype），均匀概率 `uniformProb s = s.card / Fintype.card α`；
期望 `uniformExpectation X = (∑ x, X x) / Fintype.card α`（计数权重和）；
n 个独立副本 = 乘积空间 `Fin n → α`（Fintype），独立性体现为
`Finset.prod_univ_sum` 的乘积分解（∏ᵢ∑ₓ = ∑_w∏ᵢ，即 `boost_product_event`
的计数版）。

**定理链**：
1. `hoeffding_lemma`（核心引理）：|X| ≤ 1 且 E[X] = 0 ⟹ E[e^{λX}] ≤ e^{λ²/2}。
   证明路线：exp 凸性（`convexOn_exp`，mathlib 既有）⟹ 弦上界
   e^{λx} ≤ ((1−x)/2)e^{−λ} + ((1+x)/2)e^{λ}（x ∈ [−1,1]）；取期望（E[X]=0
   消去 x·sinh 项）⟹ E[e^{λX}] ≤ cosh λ；再由 mathlib 既有引理
   `Real.cosh_le_exp_half_sq : cosh λ ≤ e^{λ²/2}`（幂级数逐项比较，(2n)! ≥ 2ⁿn!）。
2. `hoeffding_lemma_bounded`：|Y| ≤ 2 且 E[Y] = 0 ⟹ E[e^{λY}] ≤ e^{2λ²}
   （引理 1 对 Y/2 作 λ ↦ 2λ 缩放）。
3. `hoeffding_lemma_shifted`：|X| ≤ 1（均值 μ 任意）⟹ E[e^{λ(X−μ)}] ≤ e^{2λ²}。
   **诚实标注**：这里没有用完整 Hoeffding 引理（任意区间 [a,b] 的
   λ²(b−a)²/8 需额外证明 t(1−t) ≤ 1/4 型不等式）；本文件用保守上界
   |X−μ| ≤ |X| + |μ| ≤ 2，代价是常数 2 取代 1/2（仍是指数集中）。
4. `markov_counting` / `markov_exp_tail`：计数马尔可夫 + 切尔诺夫桥
   P(S ≥ t) ≤ e^{−λt}E[e^{λS}]。
5. `hoeffding_tail`（核心定理）：n 个独立副本、|X_i| ≤ 1、均值 μ ⟹
   P(X̄ − μ ≥ t) ≤ e^{−n·t²/8}（常数诚实标注：引理 3 的保守常数 2 给出
   e^{−nt²/8}；若用完整 Hoeffding 引理（b−a=2）可得 e^{−nt²/2}，
   文献中 e^{−2nt²} 对应 X ∈ [0,1]（b−a=1）的情形）。
6. `hoeffding_two_sided`（加分）：P(|X̄ − μ| ≥ t) ≤ 2·e^{−n·t²/8}
   （对称下尾 + 并集界）。

⚠ **可达性提示（v14，S9 重复实现审计发现；coordinator 已核实）**：
**本文件的 `/8` 是保守常数，而全库已有一个常数更紧的平行实现，但下游用的是本文件的松版**。
- **紧版**：`RealHyperparameterBound`（`hoeffding_tail_classic_aux`、`hoeffding_tail_classic`，
  约在该模块 554 / 762 行附近，具体行号随该文件改动而漂移，以定理名为准）
  给出 **`exp(−m·t²/(2c²))`（任意半径 `c`）** ——
  取 `c = 1` 即 **`/2`**，**比本文件的 `/8` 紧 4 倍**；
- **可达性倒挂（实测）**：`RealHoeffding` 的**直接** importer **= 22**
  （计数口径：于 `lattice/lean/*.lean` 统计 `^import RealHoeffding$` 的文件数，
  **非**传递闭包数），而 `RealHyperparameterBound` 的直接 importer **= 0**；
- **下游把 `/8` 硬编码进了 30 处陈述级位置**（`RealBanditTheory` 6、`RealEarlyStoppingStatistics` 4、
  `RealGeneralizationBound` 4、`RealDistillGeneralization` 2、`RealRademacher` 3、
  `RealHyperparameterBound` 11）；
- 注意：**硬障碍**：`RealHyperparameterBound.lean:2` **import 本文件** ⟹ **反向复用会成环**，
  **不是改一个 import 就能解决**，需先做**叶子模块下沉**（独立立项）。
- ⇒ **本文件自身没有写错**（上面两条 docstring **各自诚实**）；
  问题在于**两份 docstring 合起来不诚实**：读者从任何一侧都看不出
  **全库 7 个模块的界被 4 倍松化**。**处置：仅加本交叉引用（零风险），下沉重构另立项。**

**衔接 RealSamplingBoost**：`boost_confidence` 给出「k 轮全部 miss 概率
≤ ε^k」（幂衰减，ε 为单轮 miss 概率）；本文件把「单轮 miss 概率」这一
输入从马尔可夫/切比雪夫（多项式）升级为指数型：若训练收敛给出期望界
（RealConvergence/RealGradDescent 的 ε-终止），`hoeffding_tail` 给出
验证违背概率的 e^{−c·n·t²} 指数衰减——随机化验证的指数级置信提升。

诚实假设：α 非空（N = |α| > 0，均匀概率分母非零）、n > 0、t > 0。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 有限均匀期望（计数权重和） -/

/-- 有限集上的均匀期望：`X` 的计数加权平均值 `(∑ x, X x) / |α|`（与
`uniformProb` 同一概率空间设定：每个样本点等概率 1/|α|）。 -/
def uniformExpectation {α : Type*} [Fintype α] (X : α → ℝ) : ℝ :=
  (∑ x : α, X x) / (Fintype.card α : ℝ)

/-! ## 小引理：期望的代数性质（零均值 ⟺ 零和、|均值| ≤ 1 等） -/

/-- 期望等于 μ ⟺ 总和等于 N·μ（N = |α| ≠ 0 时）。 -/
lemma sum_eq_card_mul_mean {α : Type*} [Fintype α] {X : α → ℝ} {μ : ℝ}
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ) :
    (∑ x : α, X x) = (Fintype.card α : ℝ) * μ := by
  rw [← hmean]
  exact (mul_div_cancel₀ (∑ x : α, X x) (ne_of_gt (Nat.cast_pos.mpr hN))).symm

/-- 总和为零 ⟹ 期望为零（任意 N，含 N=0 时 0/0=0）。 -/
lemma uniformExpectation_eq_zero_of_sum_eq_zero {α : Type*} [Fintype α] {Y : α → ℝ}
    (hzero : (∑ x : α, Y x) = 0) : uniformExpectation Y = 0 := by
  unfold uniformExpectation
  rw [hzero]
  norm_num

/-- 期望为零且 N > 0 ⟹ 总和为零。 -/
lemma sum_eq_zero_of_uniformExpectation_eq_zero {α : Type*} [Fintype α] {Y : α → ℝ}
    (hN : 0 < Fintype.card α) (hzero : uniformExpectation Y = 0) : (∑ x : α, Y x) = 0 := by
  have hNne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  calc
    (∑ x : α, Y x) = ((∑ x : α, Y x) / (Fintype.card α : ℝ)) * (Fintype.card α : ℝ) := by
      rw [div_mul_cancel₀ _ hNne]
    _ = 0 := by
      unfold uniformExpectation at hzero
      rw [hzero]
      simp

/-- 中心化变量的总和为零：Σ(X − μ) = 0（当 EX = μ）。 -/
lemma sum_sub_mean_zero {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ)
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ) :
    (∑ x : α, (X x - μ)) = 0 := by
  calc
    (∑ x : α, (X x - μ)) = (∑ x : α, X x) - (∑ x : α, μ) := by rw [Finset.sum_sub_distrib]
    _ = (Fintype.card α : ℝ) * μ - (Fintype.card α : ℝ) * μ := by
      rw [sum_eq_card_mul_mean hN hmean]
      rw [Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul]
    _ = 0 := by ring

/-- 反号中心化变量的总和为零：Σ(μ − X) = 0（当 EX = μ）。 -/
lemma sum_mean_sub_zero {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ)
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ) :
    (∑ x : α, (μ - X x)) = 0 := by
  calc
    (∑ x : α, (μ - X x)) = (∑ x : α, μ) - (∑ x : α, X x) := by rw [Finset.sum_sub_distrib]
    _ = (Fintype.card α : ℝ) * μ - (Fintype.card α : ℝ) * μ := by
      rw [Finset.sum_const, Finset.card_univ]
      rw [sum_eq_card_mul_mean hN hmean]
      simp [nsmul_eq_mul]
    _ = 0 := by ring

/-- 中心化变量的期望为零。 -/
lemma uniformExpectation_sub_mean_eq_zero {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ)
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ) :
    uniformExpectation (fun x => X x - μ) = 0 :=
  uniformExpectation_eq_zero_of_sum_eq_zero (sum_sub_mean_zero μ hN hmean)

/-- |EX| ≤ 1（当 |X| ≤ 1）：均值被逐点界控制。 -/
lemma abs_mean_le_one {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ)
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ) (hb : ∀ x : α, |X x| ≤ 1) :
    |μ| ≤ 1 := by
  have habs : |∑ x : α, X x| ≤ (Fintype.card α : ℝ) := by
    calc
      |∑ x : α, X x| ≤ ∑ x : α, |X x| := Finset.abs_sum_le_sum_abs X Finset.univ
      _ ≤ ∑ x : α, (1 : ℝ) := Finset.sum_le_sum (fun x hx => hb x)
      _ = (Fintype.card α : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [nsmul_eq_mul]
  calc
    |μ| = |(∑ x : α, X x) / (Fintype.card α : ℝ)| := by
      exact (congrArg abs hmean).symm
    _ = |∑ x : α, X x| / (Fintype.card α : ℝ) := by
      have hNabs : |(Fintype.card α : ℝ)| = (Fintype.card α : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [abs_div, hNabs]
    _ ≤ (Fintype.card α : ℝ) / (Fintype.card α : ℝ) :=
      div_le_div_of_nonneg_right habs (Nat.cast_nonneg _)
    _ = 1 := by exact div_self (ne_of_gt (Nat.cast_pos.mpr hN))

/-- 偏差被 2 控制：|X − μ| ≤ 2（当 |X| ≤ 1、EX = μ）。 -/
lemma abs_deviation_le_two {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ)
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ) (hb : ∀ x : α, |X x| ≤ 1) :
    ∀ x : α, |X x - μ| ≤ 2 := by
  intro x
  have hmu : |μ| ≤ 1 := abs_mean_le_one μ hN hmean hb
  calc
    |X x - μ| ≤ |X x| + |μ| := by simpa using abs_sub_le (X x) 0 μ
    _ ≤ 1 + 1 := add_le_add (hb x) hmu
    _ = 2 := by norm_num

/-! ## 引理 1（核心）：Hoeffding 引理（|X| ≤ 1、EX = 0）
E[e^{λX}] ≤ e^{λ²/2}。证明路线：exp 凸性 ⟹ 弦上界
e^{λx} ≤ ((1−x)/2)e^{−λ} + ((1+x)/2)e^{λ}；取期望消去 E[X] = 0 的线性项
⟹ E[e^{λX}] ≤ (e^{−λ}+e^{λ})/2 = cosh λ；`Real.cosh_le_exp_half_sq`
（mathlib 既有，幂级数逐项比较）⟹ ≤ e^{λ²/2}。 -/

theorem hoeffding_lemma {α : Type*} [Fintype α] {X : α → ℝ} {lam : ℝ}
    (hN : 0 < Fintype.card α) (hzero : (∑ x : α, X x) = 0) (hb : ∀ x : α, |X x| ≤ 1) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (lam ^ 2 / 2) := by
  -- 逐点弦上界：e^{λx} ≤ ((1−x)/2)e^{−λ} + ((1+x)/2)e^{λ}（exp 凸性，convexOn_exp）
  have hchord : ∀ x : α, Real.exp (lam * X x) ≤
      ((1 - X x) / 2) * Real.exp (-lam) + ((1 + X x) / 2) * Real.exp lam := by
    intro x
    have hle1 : X x ≤ 1 := (abs_le.mp (hb x)).2
    have hge1 : -1 ≤ X x := (abs_le.mp (hb x)).1
    have ha : 0 ≤ (1 - X x) / 2 := by
      exact div_nonneg (by nlinarith [hle1]) (by norm_num)
    have hb0 : 0 ≤ (1 + X x) / 2 := by
      exact div_nonneg (by nlinarith [hge1]) (by norm_num)
    have hab : (1 - X x) / 2 + (1 + X x) / 2 = 1 := by ring
    have hchord_raw := convexOn_exp.2 (Set.mem_univ (-lam)) (Set.mem_univ lam) ha hb0 hab
    have harg : -((1 - X x) / 2 * lam) + ((1 + X x) / 2) * lam = lam * X x := by ring
    simpa [smul_eq_mul, harg] using hchord_raw
  -- 弦上界求和：∑ e^{λX} ≤ ∑ 弦
  have hsumRHS : (∑ x : α, (((1 - X x) / 2) * Real.exp (-lam) + ((1 + X x) / 2) * Real.exp lam))
      = (Fintype.card α : ℝ) * (Real.exp (-lam) + Real.exp lam) / 2 := by
    have h1 : (∑ x : α, (1 - X x)) = (Fintype.card α : ℝ) := by
      rw [Finset.sum_sub_distrib]
      rw [Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul, hzero]
    have h2 : (∑ x : α, (1 + X x)) = (Fintype.card α : ℝ) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul, hzero]
    calc
      (∑ x : α, (((1 - X x) / 2) * Real.exp (-lam) + ((1 + X x) / 2) * Real.exp lam))
          = (∑ x : α, ((1 - X x) / 2) * Real.exp (-lam)) + (∑ x : α, ((1 + X x) / 2) * Real.exp lam) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ x : α, (1 - X x) / 2) * Real.exp (-lam) + (∑ x : α, (1 + X x) / 2) * Real.exp lam := by
            rw [Finset.sum_mul, Finset.sum_mul]
      _ = ((∑ x : α, (1 - X x)) / 2) * Real.exp (-lam) + ((∑ x : α, (1 + X x)) / 2) * Real.exp lam := by
            rw [Finset.sum_div, Finset.sum_div]
      _ = ((Fintype.card α : ℝ) / 2) * Real.exp (-lam) + ((Fintype.card α : ℝ) / 2) * Real.exp lam := by
            rw [h1, h2]
      _ = (Fintype.card α : ℝ) * (Real.exp (-lam) + Real.exp lam) / 2 := by ring
  have hsum_le0 : (∑ x : α, Real.exp (lam * X x)) ≤
      ∑ x : α, ((((1 - X x) / 2) * Real.exp (-lam) + ((1 + X x) / 2) * Real.exp lam)) :=
    Finset.sum_le_sum (fun x hx => hchord x)
  -- 除以 N = |α|：E[e^{λX}] ≤ (e^{−λ}+e^{λ})/2 = cosh λ ≤ e^{λ²/2}
  have hle0 : (∑ x : α, Real.exp (lam * X x)) / (Fintype.card α : ℝ)
      ≤ (Fintype.card α : ℝ) * (Real.exp (-lam) + Real.exp lam) / 2 / (Fintype.card α : ℝ) := by
    rw [← hsumRHS]
    exact div_le_div_of_nonneg_right hsum_le0 (Nat.cast_nonneg _)
  have hle1 : (∑ x : α, Real.exp (lam * X x)) / (Fintype.card α : ℝ)
      ≤ (Real.exp (-lam) + Real.exp lam) / 2 := by
    calc
      (∑ x : α, Real.exp (lam * X x)) / (Fintype.card α : ℝ)
          ≤ (Fintype.card α : ℝ) * (Real.exp (-lam) + Real.exp lam) / 2 / (Fintype.card α : ℝ) := hle0
      _ = (Real.exp (-lam) + Real.exp lam) / 2 := by
        field_simp [ne_of_gt (Nat.cast_pos.mpr hN)]
        ring
  calc
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤ (Real.exp (-lam) + Real.exp lam) / 2 := by
      unfold uniformExpectation
      exact hle1
    _ = Real.cosh lam := by
      rw [Real.cosh_eq]
      ring
    _ ≤ Real.exp (lam ^ 2 / 2) := Real.cosh_le_exp_half_sq lam

/-! ## 引理 2：有界版本（|Y| ≤ 2、EY = 0）
E[e^{λY}] ≤ e^{2λ²}：引理 1 对 Z = Y/2（|Z| ≤ 1）作 λ ↦ 2λ 缩放。 -/

theorem hoeffding_lemma_bounded {α : Type*} [Fintype α] {Y : α → ℝ} {lam : ℝ}
    (hN : 0 < Fintype.card α) (hzero : (∑ x : α, Y x) = 0) (hb : ∀ x : α, |Y x| ≤ 2) :
    uniformExpectation (fun x => Real.exp (lam * Y x)) ≤ Real.exp (2 * lam ^ 2) := by
  have hz_zero : (∑ x : α, Y x / 2) = 0 := by
    calc
      (∑ x : α, Y x / 2) = (∑ x : α, Y x) / 2 := by rw [Finset.sum_div]
      _ = 0 := by rw [hzero]; norm_num
  have hz_b : ∀ x : α, |Y x / 2| ≤ 1 := by
    intro x
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |Y x| / 2 ≤ 2 / 2 := div_le_div_of_nonneg_right (hb x) (by norm_num : (0 : ℝ) ≤ 2)
      _ = 1 := by norm_num
  have hz := hoeffding_lemma (X := fun x => Y x / 2) (lam := 2 * lam) hN hz_zero hz_b
  -- 化简：e^{2λ·(Y/2)} = e^{λY}，(2λ)²/2 = 2λ²
  have harg : (fun x : α => Real.exp ((2 * lam) * (Y x / 2))) = fun x : α => Real.exp (lam * Y x) := by
    funext x
    congr 1
    ring
  have hz' : uniformExpectation (fun x => Real.exp (lam * Y x)) ≤ Real.exp ((2 * lam) ^ 2 / 2) := by
    simpa [harg] using hz
  convert hz' using 1
  · congr 1
    ring

/-! ## 引理 3：均值平移版本（|X| ≤ 1、EX = μ 任意）
E[e^{λ(X−μ)}] ≤ e^{2λ²}。**诚实标注**：用保守上界 |X−μ| ≤ 2（而非
完整 Hoeffding 引理的 |X−μ| 区间宽度 2 精确常数 λ²/2），常数 2 是
保守的；代价是指数 −nt²/8 而非 −nt²/2。 -/

theorem hoeffding_lemma_shifted {α : Type*} [Fintype α] {X : α → ℝ} (μ lam : ℝ)
    (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ) (hb : ∀ x : α, |X x| ≤ 1) :
    uniformExpectation (fun x => Real.exp (lam * (X x - μ))) ≤ Real.exp (2 * lam ^ 2) := by
  exact hoeffding_lemma_bounded (Y := fun x => X x - μ) (lam := lam) hN
    (sum_sub_mean_zero μ hN hmean) (abs_deviation_le_two μ hN hmean hb)

/-! ## 引理 4：计数马尔可夫界
μ{f ≥ ε} ≤ (1/ε)·E[f]（f ≥ 0，ε > 0）。证明：ε·|{ε≤f}| ≤ Σ_{ε≤f} f ≤ Σf。 -/

theorem markov_counting {α : Type*} [Fintype α] {f : α → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ x, 0 ≤ f x) :
    uniformProb (Finset.univ.filter (fun x => ε ≤ f x)) ≤ (1 / ε) * uniformExpectation f := by
  let A := Finset.univ.filter (fun x => ε ≤ f x)
  have hε_A : ε * A.card ≤ A.sum f := by
    calc
      ε * A.card = A.sum (fun _ => ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ A.sum f := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2
  have hA_le : A.sum f ≤ (Finset.univ : Finset α).sum f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (s := A) (t := Finset.univ)
    · intro x hx
      exact Finset.mem_univ _
    · intro x hx hnx
      exact hf x
  have hdiv : A.card ≤ (∑ x : α, f x) / ε := by
    have h1 : ε * A.card ≤ (∑ x : α, f x) := hε_A.trans hA_le
    exact (le_div_iff₀ hε).mpr (by simpa [mul_comm] using h1)
  unfold uniformProb uniformExpectation
  calc
    A.card / (Fintype.card α : ℝ) ≤ ((∑ x : α, f x) / ε) / (Fintype.card α : ℝ) :=
      div_le_div_of_nonneg_right hdiv (Nat.cast_nonneg _)
    _ = (1 / ε) * ((∑ x : α, f x) / (Fintype.card α : ℝ)) := by ring

/-! ## 引理 5：指数（切尔诺夫）马尔可夫桥
P(S ≥ t) ≤ e^{−λt}·E[e^{λS}]（λ > 0）。证明：{t ≤ S} ⊆ {e^{λt} ≤ e^{λS}}
（exp 单调）+ 计数马尔可夫（f = e^{λS}，阈值 e^{λt}）。 -/

theorem markov_exp_tail {α : Type*} [Fintype α] (S : α → ℝ) {t lam : ℝ} (hlam : 0 < lam) :
    uniformProb (Finset.univ.filter (fun w => t ≤ S w)) ≤
      Real.exp (-lam * t) * uniformExpectation (fun w => Real.exp (lam * S w)) := by
  have hset : Finset.univ.filter (fun w => t ≤ S w) ⊆
      Finset.univ.filter (fun w => Real.exp (lam * t) ≤ Real.exp (lam * S w)) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw.2 (le_of_lt hlam))⟩
  have hmono : uniformProb (Finset.univ.filter (fun w => t ≤ S w)) ≤
      uniformProb (Finset.univ.filter (fun w => Real.exp (lam * t) ≤ Real.exp (lam * S w))) := by
    unfold uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hset) (Nat.cast_nonneg _)
  have hmarkov := markov_counting (f := fun w => Real.exp (lam * S w)) (ε := Real.exp (lam * t))
    (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
  calc
    uniformProb (Finset.univ.filter (fun w => t ≤ S w)) ≤
        uniformProb (Finset.univ.filter (fun w => Real.exp (lam * t) ≤ Real.exp (lam * S w))) := hmono
    _ ≤ (1 / Real.exp (lam * t)) * uniformExpectation (fun w => Real.exp (lam * S w)) := hmarkov
    _ = Real.exp (-lam * t) * uniformExpectation (fun w => Real.exp (lam * S w)) := by
      congr 1
      rw [one_div, ← Real.exp_neg (lam * t)]
      congr 1
      ring

/-! ## 定理 6：核心尾界（有界零均值偏差的乘积空间版，S-形式）
n 个独立副本 Y 满足 |Y| ≤ 2、E[Y] = 0 ⟹
P(n·t ≤ Σᵢ Y(Xᵢ)) ≤ e^{−n·t²/8}。证明路线：乘积分解
E[e^{λΣY}] = ∏ᵢ E[e^{λY}] ≤ e^{2nλ²}（引理 3 型界 + `Finset.prod_univ_sum`）
+ 马尔可夫桥（引理 5），取 λ = t/4 最小化：e^{−λnt + 2nλ²} = e^{−nt²/8}。 -/

theorem hoeffding_tail_bounded {α : Type*} [Fintype α] {Y : α → ℝ} (n : ℕ)
    (hn : 0 < n) (hN : 0 < Fintype.card α) (hzero : uniformExpectation Y = 0)
    (hb : ∀ x : α, |Y x| ≤ 2) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α => (n : ℝ) * t ≤ ∑ i : Fin n, Y (w i))) ≤
      Real.exp (-(n : ℝ) * t ^ 2 / 8) := by
  let S : (Fin n → α) → ℝ := fun w => ∑ i : Fin n, Y (w i)
  let lam : ℝ := t / 4
  have hnℝ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos ht (by norm_num)
  have hzero_sum : (∑ x : α, Y x) = 0 := sum_eq_zero_of_uniformExpectation_eq_zero hN hzero
  -- E[e^{λS}] ≤ e^{2nλ²}：乘积分解 + 每变量界
  have hfunc : (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, Y (w i))))
      = fun w : Fin n → α => ∏ i : Fin n, Real.exp (lam * Y (w i)) := by
    funext w
    calc
      Real.exp (lam * (∑ i : Fin n, Y (w i))) = Real.exp (∑ i : Fin n, lam * Y (w i)) := by
        rw [Finset.mul_sum]
      _ = ∏ i : Fin n, Real.exp (lam * Y (w i)) := Real.exp_sum _ _
  have hE : uniformExpectation (fun w : Fin n → α => Real.exp (lam * S w)) ≤
      Real.exp (2 * (n : ℝ) * lam ^ 2) := by
    calc
      uniformExpectation (fun w : Fin n → α => Real.exp (lam * S w))
          = (∑ w : Fin n → α, ∏ i : Fin n, Real.exp (lam * Y (w i))) / (Fintype.card (Fin n → α) : ℝ) := by
            unfold uniformExpectation
            dsimp [S]
            rw [hfunc]
      _ = (∏ i : Fin n, ∑ x : α, Real.exp (lam * Y x)) / ((Fintype.card α : ℝ) ^ n) := by
            rw [Fintype.card_pi_const, Nat.cast_pow]
            congr 1
            rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset α))
              (f := fun i x => Real.exp (lam * Y x))]
            simp
      _ = ∏ i : Fin n, uniformExpectation (fun x => Real.exp (lam * Y x)) := by
            unfold uniformExpectation
            calc
              (∏ i : Fin n, ∑ x : α, Real.exp (lam * Y x)) / ((Fintype.card α : ℝ) ^ n)
                  = (∏ i : Fin n, ∑ x : α, Real.exp (lam * Y x)) / (∏ i : Fin n, (Fintype.card α : ℝ)) := by
                    congr 1
                    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              _ = ∏ i : Fin n, ((∑ x : α, Real.exp (lam * Y x)) / (Fintype.card α : ℝ)) := by
                    rw [Finset.prod_div_distrib]
      _ ≤ ∏ i : Fin n, Real.exp (2 * lam ^ 2) := by
            apply Finset.prod_le_prod
            · intro i hi
              unfold uniformExpectation
              exact div_nonneg (Finset.sum_nonneg (fun x hx => Real.exp_nonneg _)) (Nat.cast_nonneg _)
            · intro i hi
              exact hoeffding_lemma_bounded (Y := Y) (lam := lam) hN hzero_sum hb
      _ = Real.exp (2 * (n : ℝ) * lam ^ 2) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [← Real.exp_nat_mul (2 * lam ^ 2) n]
            congr 1
            ring
  -- 马尔可夫桥 + λ = t/4 最小化
  have hmarkov := markov_exp_tail (S := S) (t := (n : ℝ) * t) (lam := lam) hlam
  have hmain : uniformProb (Finset.univ.filter (fun w : Fin n → α => (n : ℝ) * t ≤ S w)) ≤
      Real.exp (-(n : ℝ) * t ^ 2 / 8) := by
    calc
      uniformProb (Finset.univ.filter (fun w : Fin n → α => (n : ℝ) * t ≤ S w))
          ≤ Real.exp (-lam * ((n : ℝ) * t)) * uniformExpectation (fun w => Real.exp (lam * S w)) := hmarkov
      _ ≤ Real.exp (-lam * ((n : ℝ) * t)) * Real.exp (2 * (n : ℝ) * lam ^ 2) :=
            mul_le_mul_of_nonneg_left hE (Real.exp_nonneg _)
      _ = Real.exp (-(n : ℝ) * t ^ 2 / 8) := by
            rw [← Real.exp_add]
            congr 1
            dsimp [lam]
            field_simp
            ring
  simpa [S] using hmain

/-! ## 定理 7（核心）：Hoeffding 尾界（|X_i| ≤ 1、均值 μ）
P(X̄ − μ ≥ t) ≤ e^{−n·t²/8}，其中 X̄ = (Σᵢ X(Xᵢ))/n。
证明：Y = X − μ 满足 |Y| ≤ 2、E[Y] = 0（定理 6）；事件改写
{t ≤ X̄ − μ} = {n·t ≤ Σᵢ (X(Xᵢ) − μ)}。 -/

theorem hoeffding_tail {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ) (n : ℕ)
    (hn : 0 < n) (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ)
    (hb : ∀ x : α, |X x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ (∑ i : Fin n, X (w i)) / n - μ)) ≤
      Real.exp (-(n : ℝ) * t ^ 2 / 8) := by
  -- 事件改写 1：{t ≤ (ΣX)/n − μ} = {t ≤ (Σ(X−μ))/n}
  have hset : Finset.univ.filter (fun w : Fin n → α => t ≤ (∑ i : Fin n, X (w i)) / n - μ)
      = Finset.univ.filter (fun w : Fin n → α => t ≤ (∑ i : Fin n, (X (w i) - μ)) / n) := by
    apply Finset.filter_congr
    intro w hw
    have hsum : (∑ i : Fin n, X (w i)) / n - μ = (∑ i : Fin n, (X (w i) - μ)) / n := by
      calc
        (∑ i : Fin n, X (w i)) / n - μ = ((∑ i : Fin n, X (w i)) - (n : ℝ) * μ) / n := by
          field_simp [ne_of_gt (Nat.cast_pos.mpr hn)]
        _ = (∑ i : Fin n, (X (w i) - μ)) / n := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]
    rw [hsum]
  -- 事件改写 2：{t ≤ (Σ(X−μ))/n} = {n·t ≤ Σ(X−μ)}
  have hset2 : Finset.univ.filter (fun w : Fin n → α => t ≤ (∑ i : Fin n, (X (w i) - μ)) / n)
      = Finset.univ.filter (fun w : Fin n → α => (n : ℝ) * t ≤ ∑ i : Fin n, (X (w i) - μ)) := by
    apply Finset.filter_congr
    intro w hw
    rw [le_div_iff₀ (Nat.cast_pos.mpr hn)]
    simp [mul_comm]
  rw [hset, hset2]
  -- 定理 6：Y = X − μ
  exact hoeffding_tail_bounded (Y := fun x => X x - μ) n hn hN
    (uniformExpectation_sub_mean_eq_zero μ hN hmean) (abs_deviation_le_two μ hN hmean hb) ht

/-! ## 定理 8（加分）：双边 Hoeffding 界
P(|X̄ − μ| ≥ t) ≤ 2·e^{−n·t²/8}。证明：{t ≤ |a|} ⊆ {t ≤ a} ∪ {a ≤ −t}
（|a| ≥ t ⟹ a ≥ t 或 a ≤ −t）+ 上尾界（定理 7）+ 对称下尾界
（对 Y' = μ − X 用定理 6）+ 并集界（card_union_le）。 -/

theorem hoeffding_two_sided {α : Type*} [Fintype α] [DecidableEq α] {X : α → ℝ} (μ : ℝ) (n : ℕ)
    (hn : 0 < n) (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ)
    (hb : ∀ x : α, |X x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ |(∑ i : Fin n, X (w i)) / n - μ|)) ≤
      2 * Real.exp (-(n : ℝ) * t ^ 2 / 8) := by
  let A := Finset.univ.filter (fun w : Fin n → α => t ≤ |(∑ i : Fin n, X (w i)) / n - μ|)
  let B := Finset.univ.filter (fun w : Fin n → α => t ≤ (∑ i : Fin n, X (w i)) / n - μ)
  let C := Finset.univ.filter (fun w : Fin n → α => (∑ i : Fin n, X (w i)) / n - μ ≤ -t)
  have hsub : A ⊆ B ∪ C := by
    intro w hw
    have hA : t ≤ |(∑ i : Fin n, X (w i)) / n - μ| := (Finset.mem_filter.mp hw).2
    let a := (∑ i : Fin n, X (w i)) / n - μ
    have hcases : t ≤ a ∨ a ≤ -t := by
      by_cases h1 : t ≤ a
      · exact Or.inl h1
      · right
        by_cases h2 : 0 ≤ a
        · have : |a| = a := abs_of_nonneg h2
          exact False.elim (h1 (by simpa [a, this] using hA))
        · have : |a| = -a := abs_of_neg (lt_of_not_ge h2)
          have htna : t ≤ -a := by simpa [a, this] using hA
          exact neg_le_neg_iff.mp (by simpa using htna)
    rcases hcases with hl | hr
    · rw [Finset.mem_union]
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [a] using hl⟩
    · rw [Finset.mem_union]
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [a] using hr⟩
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
  have hB : uniformProb B ≤ Real.exp (-(n : ℝ) * t ^ 2 / 8) := hoeffding_tail μ n hn hN hmean hb ht
  have hC : uniformProb C ≤ Real.exp (-(n : ℝ) * t ^ 2 / 8) := by
    -- 下尾 = 上尾应用于 Y' = μ − X（E[Y'] = 0，|Y'| ≤ 2）
    let Y' : α → ℝ := fun x => μ - X x
    have hY'b : ∀ x : α, |Y' x| ≤ 2 := by
      intro x
      have hmu : |μ| ≤ 1 := abs_mean_le_one μ hN hmean hb
      calc
        |Y' x| = |μ - X x| := rfl
        _ ≤ |μ| + |X x| := by simpa using abs_sub_le μ 0 (X x)
        _ ≤ 1 + 1 := add_le_add hmu (hb x)
        _ = 2 := by norm_num
    have hY'zero : uniformExpectation Y' = 0 :=
      uniformExpectation_eq_zero_of_sum_eq_zero (sum_mean_sub_zero μ hN hmean)
    have hsetC : C = Finset.univ.filter (fun w : Fin n → α => (n : ℝ) * t ≤ ∑ i : Fin n, Y' (w i)) := by
      apply Finset.filter_congr
      intro w hw
      have hrewrite : (∑ i : Fin n, (μ - X (w i))) / n = -((∑ i : Fin n, X (w i)) / n - μ) := by
        calc
          (∑ i : Fin n, (μ - X (w i))) / n = ((∑ i : Fin n, μ) - (∑ i : Fin n, X (w i))) / n := by
            rw [Finset.sum_sub_distrib]
          _ = ((n : ℝ) * μ - (∑ i : Fin n, X (w i))) / n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
          _ = -((∑ i : Fin n, X (w i)) / n - μ) := by
            field_simp [ne_of_gt (Nat.cast_pos.mpr hn)]
      calc
        ((∑ i : Fin n, X (w i)) / n - μ ≤ -t) ↔ (t ≤ -((∑ i : Fin n, X (w i)) / n - μ)) := by
          simpa using (neg_le_neg_iff (a := -t) (b := (∑ i : Fin n, X (w i)) / n - μ)).symm
        _ ↔ (t ≤ (∑ i : Fin n, (μ - X (w i))) / n) := by rw [hrewrite]
        _ ↔ ((n : ℝ) * t ≤ ∑ i : Fin n, (μ - X (w i))) := by
          constructor
          · intro h
            have h' : t * (n : ℝ) ≤ ∑ i : Fin n, (μ - X (w i)) :=
              (le_div_iff₀ (a := t) (b := (∑ i : Fin n, (μ - X (w i)))) (c := (n : ℝ))
                (Nat.cast_pos.mpr hn)).mp h
            simpa [mul_comm] using h'
          · intro h
            have h' : t * (n : ℝ) ≤ ∑ i : Fin n, (μ - X (w i)) := by
              simpa [mul_comm] using h
            exact (le_div_iff₀ (a := t) (b := (∑ i : Fin n, (μ - X (w i)))) (c := (n : ℝ))
              (Nat.cast_pos.mpr hn)).mpr h'
        _ ↔ ((n : ℝ) * t ≤ ∑ i : Fin n, Y' (w i)) := by
          simp [Y']
    rw [hsetC]
    exact hoeffding_tail_bounded (Y := Y') n hn hN hY'zero hY'b ht
  calc
    uniformProb A ≤ uniformProb (B ∪ C) := hmono
    _ ≤ uniformProb B + uniformProb C := hsubadd
    _ ≤ Real.exp (-(n : ℝ) * t ^ 2 / 8) + Real.exp (-(n : ℝ) * t ^ 2 / 8) := add_le_add hB hC
    _ = 2 * Real.exp (-(n : ℝ) * t ^ 2 / 8) := by ring

/-! ## 注：与 RealSamplingBoost 的衔接
`boost_confidence`（RealSamplingBoost）把「单轮 miss 概率 ≤ ε」放大为
「k 轮全 miss ≤ ε^k」（置信度指数逼近 1）；本文件把「单轮 miss 概率」的
来源从马尔可夫/切比雪夫（多项式）升级为 Hoeffding 指数型尾界：
`hoeffding_tail` 给出 P(X̄ − μ ≥ t) ≤ e^{−n·t²/8}，代入
RealConvergence/RealGradDescent 的 ε-终止（期望界）即得验证违背概率的
e^{−c·n·t²} 指数衰减——随机化验证从多项式提升为指数级集中。 -/

end Lattice
