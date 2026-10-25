import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: Bernstein 型尾界 —— 方差敏感的指数集中（有限计数概率空间）

方向（§5 验证行「集中不等式 / Bernstein」）：RealHoeffding 的 Hoeffding 尾界
`hoeffding_tail` 给出 P(X̄ − μ ≥ t) ≤ e^{−n·t²/8}，**只依赖有界性，与方差无关**。
本文件给出**方差敏感**（variance-sensitive）的改进：指数矩上界按二阶矩
E[X²]（零均值时的方差）而非最坏情形界 1 给出，从而当真实方差很小时，
尾界显著优于 Hoeffding。

**设定（衔接 RealSamplingBoost / RealHoeffding 的有限计数概率空间）**：
样本空间 α 有限（Fintype），均匀概率 `uniformProb`，期望 `uniformExpectation`，
二阶矩 `uniformSecondMoment X = E[X²]`；n 个独立副本 = 乘积空间
`Fin n → α`，独立性用 `Finset.prod_univ_sum` 的乘积分解。

**定理链**：
1. `exp_mul_le_one_add_add_sq`（逐点二次 Taylor 界，本文件起点）：
   λ ∈ [0,1]、|x| ≤ 1 ⟹ e^{λx} ≤ 1 + λx + (λx)²。
   证明：λ ∈ [0,1]、|x| ≤ 1 ⟹ |λx| ≤ 1，直接引用 mathlib 既有二阶 Taylor
   余项界 `Real.abs_exp_sub_one_sub_id_le : |e^t − 1 − t| ≤ t²`（|t| ≤ 1）。
   **诚实标注**：完整 Bernstein 的逐点界是
   e^{λx} ≤ 1 + λx + x²(e^λ − 1 − λ)（Bennett 型，对**所有** λ ≥ 0 成立），
   本文件没有走 Bennett 路线（需 g(x)=(e^{λx}−1−λx)/x² 单调性这一额外微积分），
   而用 λ ≤ 1 的保守二次界，代价是后面常数从 2 变到 4。
2. `bernstein_lemma`（核心引理，方差敏感指数矩）：|X| ≤ 1、EX = 0、
   λ ∈ [0,1] ⟹ E[e^{λX}] ≤ e^{λ²·E[X²]}。
   证明：逐点界求和（ΣX = 0 消去线性项）⟹ E[e^{λX}] ≤ 1 + λ²·E[X²]
   ≤ e^{λ²E[X²]}（`Real.add_one_le_exp`）。
   文献 Bernstein 引理为 e^{λ²σ²/2·1/(1−λ/3)}（λ < 3）；本版 λ ≤ 1、常数 1
   是**保守**的（λ=1 时 exp(σ²) vs 文献 exp(0.75σ²)）。
3. `bernstein_mgf_product`：n 个独立副本 ⟹ E[e^{λΣY}] ≤ e^{n·λ²·E[Y²]}。
4. `bernstein_tail`（核心尾界，方差版子高斯界）：n 个独立副本、|Y| ≤ 1、
   E[Y] = 0、V = E[Y²] > 0、t ≤ 2nV ⟹
   P(Σᵢ Y(Yᵢ) ≥ t) ≤ e^{−t²/(4nV)}。
   证明路线：乘积分解（定理 3）+ 指数马尔可夫桥（`markov_exp_tail`，RealHoeffding），
   取 λ = t/(2nV) ∈ [0,1]（t ≤ 2nV 保证）：e^{−λt+nλ²V} = e^{−t²/(4nV)}。
   **诚实标注**：常数 4nV 而非 Bernstein 的 2nV（保守）；且要求 t ≤ 2nV
   （λ ≤ 1 的使用范围，超出时 λ=1 截断只给出线性衰减 e^{−t+nV}，
   不像 Hoeffding 那样对一切 t 都给二次衰减）。与已证的
   `hoeffding_tail`（RealHoeffding，和形式 e^{−s²/(8n)}，保守常数来自
   |X−μ| ≤ 2）比较：V = E[Y²] ≤ 1 使 4nV ≤ 8n，故本界**始终不弱于**
   `hoeffding_tail`（V = 1 时紧一倍）；但与由 `hoeffding_lemma`
   （常数 λ²/2）直接得的锐利版 e^{−s²/(2n)} 相比，仅当 V < 1/2 时更紧，
   V > 1/2 时更松——这是保守常数 1（λ ≤ 1 截断）的代价。
5. `bernstein_tail_centered`（均值版本，真实方差不缩放）：|X| ≤ 1、
   E[X] = μ，Var = E[(X−μ)²] =: σ²，σ² > 0、t ≤ nσ² ⟹
   P(Σᵢ(X(Xᵢ)−μ) ≥ t) ≤ e^{−t²/(4nσ²)}。
   证明：Y = X − μ 满足 |Y| ≤ 2，对 Z = Y/2（|Z| ≤ 1）用定理 4，
   E[Z²] = σ²/4，得 e^{−t'²/(4n·σ²/4)} = e^{−t'²/(nσ²)}（t' = t/2 缩放）。
   **⚠ 文件头校准（Z1-2，v14）**：本条**旧稿**曾写「`t ≤ nσ²/2`、
   `e^{−t²/(nσ²)}`」——**与代码不符的旧稿**。代数复核：Z = Y/2 使
   ΣZ = ΣY/2 ⟹ 事件 `{t ≤ ΣY}` = `{t/2 ≤ ΣZ}`（t' = t/2）；
   定理 4 要求 `t' ≤ 2nV'`，其中 `V' = E[Z²] = σ²/4`，即
   `t/2 ≤ nσ²/2 ⟺ t ≤ nσ²`（**不是 `nσ²/2`**）；界为
   `exp(−(t/2)²/(4n·σ²/4)) = exp(−(t²/4)/(nσ²)) = exp(−t²/(4nσ²))`
   （**不是 `e^{−t²/(nσ²)}`**）。⟹ **代码对、旧稿头错**，此处已改为与
   `bernstein_tail_centered`（`RealBernstein.lean:263/:266`）逐字一致。
6. `bernstein_example`：具体数值实例（Rademacher 型 ±1，n=2）。

诚实假设：α 非空（N > 0，均匀概率分母非零）、n > 0、t > 0、
V = E[Y²] > 0（V = 0 时 Y ≡ 0，事件为空，界平凡但除法退化，故显式假设）。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 二阶矩（零均值时的方差） -/

/-- 有限均匀期望下的二阶矩：`E[X²] = (∑ x, X x ^ 2) / |α|`
（零均值时即为方差 Var(X) = E[X²] − (EX)² = E[X²]）。 -/
def uniformSecondMoment {α : Type*} [Fintype α] (X : α → ℝ) : ℝ :=
  uniformExpectation (fun x => X x ^ 2)

/-- 二阶矩非负（逐项平方非负求和除以非负总数）。 -/
lemma uniformSecondMoment_nonneg {α : Type*} [Fintype α] (X : α → ℝ) :
    0 ≤ uniformSecondMoment X := by
  unfold uniformSecondMoment uniformExpectation
  exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-- 二阶矩的求和刻画：`E[X²] = (∑ x, X x ^ 2) / |α|`。 -/
lemma uniformSecondMoment_eq {α : Type*} [Fintype α] (X : α → ℝ) :
    uniformSecondMoment X = (∑ x : α, X x ^ 2) / (Fintype.card α : ℝ) := rfl

/-! ## 引理 1：逐点二次 Taylor 界
λ ∈ [0,1]、|x| ≤ 1 ⟹ e^{λx} ≤ 1 + λx + (λx)²。
证明：|λx| ≤ 1（λ ≤ 1、|x| ≤ 1）⟹ 引用 `Real.abs_exp_sub_one_sub_id_le`
（|e^t − 1 − t| ≤ t²，|t| ≤ 1）⟹ e^{λx} − 1 − λx ≤ |…| ≤ (λx)²。 -/

lemma exp_mul_le_one_add_add_sq {lam x : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hx : |x| ≤ 1) :
    Real.exp (lam * x) ≤ 1 + lam * x + (lam * x) ^ 2 := by
  have habs : |lam * x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlam0]
    calc
      lam * |x| ≤ 1 * 1 := mul_le_mul hlam1 hx (abs_nonneg x) (by norm_num)
      _ = 1 := by ring
  have h := Real.abs_exp_sub_one_sub_id_le habs
  have h' : Real.exp (lam * x) - 1 - lam * x ≤ (lam * x) ^ 2 :=
    le_trans (le_abs_self _) h
  linarith

/-! ## 引理 2（核心）：Bernstein 引理 —— 方差敏感指数矩界
|X| ≤ 1、EX = 0、λ ∈ [0,1] ⟹ E[e^{λX}] ≤ e^{λ²·E[X²]}。
证明：逐点二次界（引理 1）求和，ΣX = 0 消去线性项，除以 N 得
E[e^{λX}] ≤ 1 + λ²E[X²]，再由 `Real.add_one_le_exp`（1 + u ≤ e^u）。 -/

theorem bernstein_lemma {α : Type*} [Fintype α] {X : α → ℝ} {lam : ℝ}
    (hN : 0 < Fintype.card α) (hzero : (∑ x : α, X x) = 0)
    (hb : ∀ x : α, |X x| ≤ 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤
      Real.exp (lam ^ 2 * uniformSecondMoment X) := by
  have hNpos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hN
  -- 逐点二次界求和
  have hpt : ∀ x : α, Real.exp (lam * X x) ≤ 1 + lam * X x + (lam * X x) ^ 2 :=
    fun x => exp_mul_le_one_add_add_sq hlam0 hlam1 (hb x)
  have hsum : (∑ x : α, Real.exp (lam * X x)) ≤
      ∑ x : α, (1 + lam * X x + (lam * X x) ^ 2) :=
    Finset.sum_le_sum (fun x _ => hpt x)
  -- 右侧求和值 = N + λ²·Σ X²
  have hsumval : (∑ x : α, (1 + lam * X x + (lam * X x) ^ 2))
      = (Fintype.card α : ℝ) + lam ^ 2 * (∑ x : α, X x ^ 2) := by
    have hA : (∑ x : α, (1 : ℝ)) = (Fintype.card α : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hB : (∑ x : α, lam * X x) = lam * (∑ x : α, X x) := by
      rw [Finset.mul_sum]
    have hC : (∑ x : α, (lam * X x) ^ 2) = lam ^ 2 * (∑ x : α, X x ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC, hzero]
    ring
  -- 除以 N：E[e^{λX}] ≤ 1 + λ²·E[X²]
  have hdiv : (∑ x : α, Real.exp (lam * X x)) / (Fintype.card α : ℝ) ≤
      ((Fintype.card α : ℝ) + lam ^ 2 * (∑ x : α, X x ^ 2)) / (Fintype.card α : ℝ) := by
    rw [← hsumval]
    exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
  have halg : ((Fintype.card α : ℝ) + lam ^ 2 * (∑ x : α, X x ^ 2)) / (Fintype.card α : ℝ)
      = 1 + lam ^ 2 * uniformSecondMoment X := by
    unfold uniformSecondMoment uniformExpectation
    field_simp
  calc
    uniformExpectation (fun x => Real.exp (lam * X x))
        ≤ 1 + lam ^ 2 * uniformSecondMoment X := by
          unfold uniformExpectation
          exact hdiv.trans_eq halg
    _ ≤ Real.exp (lam ^ 2 * uniformSecondMoment X) := by
          simpa [add_comm] using Real.add_one_le_exp (lam ^ 2 * uniformSecondMoment X)

/-! ## 定理 3：乘积分解 —— n 个独立副本的指数矩
E[e^{λΣᵢY(Yᵢ)}] = ∏ᵢ E[e^{λY}] ≤ e^{n·λ²·E[Y²]}。
证明：`Finset.prod_univ_sum`（∏ᵢ∑ₓ = ∑_w∏ᵢ）把乘积空间的期望分解为
n 个单坐标期望之积，每个 ≤ e^{λ²E[Y²]}（引理 2）。 -/

theorem bernstein_mgf_product {α : Type*} [Fintype α] {Y : α → ℝ} (n : ℕ)
    (_hn : 0 < n) (hN : 0 < Fintype.card α) (hzero : uniformExpectation Y = 0)
    (hb : ∀ x : α, |Y x| ≤ 1) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * ∑ i : Fin n, Y (w i))) ≤
      Real.exp ((n : ℝ) * lam ^ 2 * uniformSecondMoment Y) := by
  have hzero_sum : (∑ x : α, Y x) = 0 := sum_eq_zero_of_uniformExpectation_eq_zero hN hzero
  have hfunc : (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, Y (w i))))
      = fun w : Fin n → α => ∏ i : Fin n, Real.exp (lam * Y (w i)) := by
    funext w
    calc
      Real.exp (lam * (∑ i : Fin n, Y (w i))) = Real.exp (∑ i : Fin n, lam * Y (w i)) := by
        rw [Finset.mul_sum]
      _ = ∏ i : Fin n, Real.exp (lam * Y (w i)) := Real.exp_sum _ _
  calc
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, Y (w i))))
        = (∏ i : Fin n, ∑ x : α, Real.exp (lam * Y x)) / ((Fintype.card α : ℝ) ^ n) := by
          unfold uniformExpectation
          rw [hfunc]
          rw [Fintype.card_pi_const, Nat.cast_pow]
          congr 1
          rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset α))
            (f := fun i x => Real.exp (lam * Y x))]
          simp
    _ = ∏ i : Fin n, uniformExpectation (fun x => Real.exp (lam * Y x)) := by
          unfold uniformExpectation
          calc
            (∏ i : Fin n, ∑ x : α, Real.exp (lam * Y x)) / ((Fintype.card α : ℝ) ^ n)
                = (∏ i : Fin n, ∑ x : α, Real.exp (lam * Y x)) /
                    (∏ i : Fin n, (Fintype.card α : ℝ)) := by
                  congr 1
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ = ∏ i : Fin n, ((∑ x : α, Real.exp (lam * Y x)) / (Fintype.card α : ℝ)) := by
                  rw [Finset.prod_div_distrib]
    _ ≤ ∏ i : Fin n, Real.exp (lam ^ 2 * uniformSecondMoment Y) := by
          apply Finset.prod_le_prod
          · intro i _
            unfold uniformExpectation
            exact div_nonneg (Finset.sum_nonneg (fun x _ => Real.exp_nonneg _))
              (Nat.cast_nonneg _)
          · intro i _
            exact bernstein_lemma hN hzero_sum hb hlam0 hlam1
    _ = Real.exp ((n : ℝ) * lam ^ 2 * uniformSecondMoment Y) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← Real.exp_nat_mul]
          congr 1
          ring

/-! ## 定理 4（核心）：Bernstein 尾界（方差版子高斯界）
n 个独立副本、|Y| ≤ 1、E[Y] = 0、V = E[Y²] > 0、t ≤ 2nV ⟹
P(Σᵢ Y(Yᵢ) ≥ t) ≤ e^{−t²/(4nV)}。
证明：指数马尔可夫桥 `markov_exp_tail`（RealHoeffding）+
定理 3（E[e^{λS}] ≤ e^{nλ²V}），取 λ = t/(2nV) ∈ [0,1]（t ≤ 2nV）。 -/

theorem bernstein_tail {α : Type*} [Fintype α] {Y : α → ℝ} (n : ℕ)
    (hn : 0 < n) (hN : 0 < Fintype.card α) (hzero : uniformExpectation Y = 0)
    (hb : ∀ x : α, |Y x| ≤ 1) (hV : 0 < uniformSecondMoment Y)
    {t : ℝ} (ht : 0 < t) (htV : t ≤ 2 * (n : ℝ) * uniformSecondMoment Y) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, Y (w i))) ≤
      Real.exp (-t ^ 2 / (4 * (n : ℝ) * uniformSecondMoment Y)) := by
  let S : (Fin n → α) → ℝ := fun w => ∑ i : Fin n, Y (w i)
  let V : ℝ := uniformSecondMoment Y
  let lam : ℝ := t / (2 * (n : ℝ) * V)
  have hnℝ : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hVpos : 0 < V := hV
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnℝ
  have hden : 0 < 2 * (n : ℝ) * V := mul_pos (mul_pos (by norm_num) hnℝ) hVpos
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg (le_of_lt ht) (le_of_lt hden)
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    exact (div_le_one hden).mpr (by simpa [V] using htV)
  -- 指数矩界
  have hmgf : uniformExpectation (fun w : Fin n → α => Real.exp (lam * S w)) ≤
      Real.exp ((n : ℝ) * lam ^ 2 * V) := by
    simpa [S, V] using bernstein_mgf_product (Y := Y) n hn hN hzero hb hlam0 hlam1
  -- 指数马尔可夫桥
  have hmarkov := markov_exp_tail (S := S) (t := t) (lam := lam) (by
    dsimp [lam]
    exact div_pos ht hden)
  -- 指数化简：−λt + nλ²V = −t²/(4nV)
  have hexp : -lam * t + (n : ℝ) * lam ^ 2 * V =
      -t ^ 2 / (4 * (n : ℝ) * V) := by
    dsimp [lam]
    field_simp
    ring
  calc
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, Y (w i)))
        = uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ S w)) := by simp [S]
    _ ≤ Real.exp (-lam * t) * uniformExpectation (fun w => Real.exp (lam * S w)) := hmarkov
    _ ≤ Real.exp (-lam * t) * Real.exp ((n : ℝ) * lam ^ 2 * V) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-lam * t + (n : ℝ) * lam ^ 2 * V) := by rw [← Real.exp_add]
    _ = Real.exp (-t ^ 2 / (4 * (n : ℝ) * V)) := by rw [hexp]
    _ = Real.exp (-t ^ 2 / (4 * (n : ℝ) * uniformSecondMoment Y)) := by rfl

/-! ## 定理 5：均值版本（真实方差，不缩放）
|X| ≤ 1、E[X] = μ、σ² = E[(X−μ)²] > 0、t ≤ nσ² ⟹
P(Σᵢ(X(Xᵢ)−μ) ≥ t) ≤ e^{−t²/(4nσ²)}。
证明：Y = X − μ 满足 |Y| ≤ 2（`abs_deviation_le_two`）与 E[Y] = 0
（`uniformExpectation_sub_mean_eq_zero`）；令 Z = Y/2（|Z| ≤ 1），
E[Z²] = σ²/4；对 Z 用定理 4、阈值取 t/2（事件 {t ≤ ΣY} = {t/2 ≤ ΣZ}，
因 ΣZ = ΣY/2）：t/2 ≤ 2n·(σ²/4) ⟺ t ≤ nσ²，
e^{−(t/2)²/(4n·σ²/4)} = e^{−t²/(4nσ²)}。**诚实标注**：缩放 Z = Y/2 使
常数从 4 保持为 4，但可用区间从 t ≤ 2nV 收紧为 t ≤ nV。 -/

theorem bernstein_tail_centered {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ) (n : ℕ)
    (hn : 0 < n) (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ)
    (hb : ∀ x : α, |X x| ≤ 1) (hV : 0 < uniformSecondMoment (fun x => X x - μ))
    {t : ℝ} (ht : 0 < t) (htV : t ≤ (n : ℝ) * uniformSecondMoment (fun x => X x - μ)) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        t ≤ ∑ i : Fin n, (X (w i) - μ))) ≤
      Real.exp (-t ^ 2 / (4 * (n : ℝ) * uniformSecondMoment (fun x => X x - μ))) := by
  let Y : α → ℝ := fun x => X x - μ
  let Z : α → ℝ := fun x => Y x / 2
  have hnℝ : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hYzero : uniformExpectation Y = 0 :=
    uniformExpectation_sub_mean_eq_zero μ hN hmean
  have hYsum : (∑ x : α, Y x) = 0 := sum_eq_zero_of_uniformExpectation_eq_zero hN hYzero
  have hYb : ∀ x : α, |Y x| ≤ 2 := abs_deviation_le_two μ hN hmean hb
  have hZb : ∀ x : α, |Z x| ≤ 1 := by
    intro x
    dsimp [Z]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |Y x| / 2 ≤ 2 / 2 := div_le_div_of_nonneg_right (hYb x) (by norm_num)
      _ = 1 := by norm_num
  have hZzero : uniformExpectation Z = 0 := by
    dsimp [Z]
    unfold uniformExpectation
    rw [← Finset.sum_div, hYsum]
    norm_num
  -- E[Z²] = E[Y²]/4
  have hZsq : uniformSecondMoment Z = uniformSecondMoment Y / 4 := by
    unfold uniformSecondMoment uniformExpectation
    have hsumZ : (∑ x : α, Z x ^ 2) = (∑ x : α, Y x ^ 2) / 4 := by
      calc
        (∑ x : α, Z x ^ 2) = ∑ x : α, (Y x / 2) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          dsimp [Z]
        _ = (∑ x : α, Y x ^ 2) / 4 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x _
          ring
    rw [hsumZ]
    ring
  have hZV : 0 < uniformSecondMoment Z := by
    rw [hZsq]
    exact div_pos hV (by norm_num)
  -- 事件改写：{t/2 ≤ Σ Z} = {t ≤ Σ Y}，用定理 4 于 Z、阈值 t/2
  have hsub : t / 2 ≤ 2 * (n : ℝ) * uniformSecondMoment Z := by
    rw [hZsq]
    have h2 : 2 * (n : ℝ) * (uniformSecondMoment Y / 4) =
        (n : ℝ) * uniformSecondMoment Y / 2 := by ring
    rw [h2]
    linarith [htV]
  have hkey := bernstein_tail (Y := Z) n hn hN hZzero hZb hZV
    (by linarith : 0 < t / 2) hsub
  -- Σ Z = Σ Y / 2
  have hsumZ : ∀ w : Fin n → α, (∑ i : Fin n, Z (w i)) = (∑ i : Fin n, Y (w i)) / 2 := by
    intro w
    dsimp [Z]
    rw [Finset.sum_div]
  have hset : Finset.univ.filter (fun w : Fin n → α =>
        t / 2 ≤ ∑ i : Fin n, Z (w i))
      = Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, Y (w i)) := by
    apply Finset.filter_congr
    intro w _
    rw [hsumZ w]
    constructor <;> intro h <;> linarith
  rw [hset] at hkey
  -- 指数常数化简：−(t/2)²/(4n·(V/4)) = −t²/(4nV)
  have hexp : -(t / 2) ^ 2 / (4 * (n : ℝ) * uniformSecondMoment Z) =
      -t ^ 2 / (4 * (n : ℝ) * uniformSecondMoment Y) := by
    rw [hZsq]
    field_simp
    ring
  rw [hexp] at hkey
  simpa [Y] using hkey

/-! ## 定理 6：具体数值实例（Rademacher ±1，n = 2）
α = Fin 2，Y = (a ↦ if a = 0 then 1 else −1)（两个点等权，EX = 0，|Y| ≤ 1，
E[Y²] = 1）；n = 2 个独立副本，事件 {2 ≤ Y(Y₀)+Y(Y₁)} 的概率 = 1/4
≤ e^{−1/2} = e^{−t²/(4nV)}（t = 2、n = 2、V = 1）。 -/

/-- Rademacher 型 ±1 变量（Fin 2 上的零均值有界函数，E[Y²] = 1）。 -/
def rademacher : Fin 2 → ℝ := fun a => if a = 0 then 1 else -1

lemma rademacher_sum_zero : (∑ a : Fin 2, rademacher a) = 0 := by
  rw [Fin.sum_univ_two]
  norm_num [rademacher]

lemma rademacher_abs_le_one : ∀ a : Fin 2, |rademacher a| ≤ 1 := by
  intro a
  fin_cases a <;> norm_num [rademacher]

lemma rademacher_second_moment : uniformSecondMoment rademacher = 1 := by
  unfold uniformSecondMoment uniformExpectation
  rw [show (∑ x : Fin 2, rademacher x ^ 2) = 2 from by
    rw [Fin.sum_univ_two]
    norm_num [rademacher]]
  norm_num

/-- 具体实例：Rademacher ±1、n = 2、阈值 t = 2 的 Bernstein 尾界
（真实概率 1/4，界 e^{−1/2}：−t²/(4nV) = −4/8 = −1/2）。 -/
theorem bernstein_example :
    uniformProb (Finset.univ.filter (fun w : Fin 2 → Fin 2 =>
        2 ≤ ∑ i : Fin 2, rademacher (w i))) ≤ Real.exp (-(1 / 2)) := by
  have h := bernstein_tail (Y := rademacher) 2 (by norm_num)
    (by norm_num : 0 < Fintype.card (Fin 2))
    (uniformExpectation_eq_zero_of_sum_eq_zero rademacher_sum_zero) rademacher_abs_le_one
    (by rw [rademacher_second_moment]; norm_num)
    (by norm_num : (0 : ℝ) < 2)
    (by rw [rademacher_second_moment]; norm_num)
  rw [rademacher_second_moment] at h
  exact le_trans h (Real.exp_le_exp.mpr (by norm_num))

/-! ## 注：与 RealHoeffding / RealSamplingBoost 的衔接
`hoeffding_tail`（RealHoeffding）给出和形式 e^{−s²/(8n)}（保守常数来自
|X−μ| ≤ 2），与方差无关；本文件 `bernstein_tail` 给出方差敏感的
e^{−t²/(4nV)}（V = E[Y²]，t ≤ 2nV）。因 V ≤ 1，4nV ≤ 8n，本界始终不弱于
`hoeffding_tail`；与由 `hoeffding_lemma` 常数 λ²/2 直接得的锐利版
e^{−t²/(2n)} 相比，仅 V < 1/2 时更紧。两条界都通过 `boost_confidence`
（RealSamplingBoost）把「单轮 miss 概率」放大为 k 轮验证置信度 ≥ 1 − ε^k
——方差小时 Bernstein 给出更强的单轮界。

**后续工作（诚实标注）**：完整 Bernstein 引理（λ < 3、常数 1/(1−λ/3)）
需要 Bennett 逐点不等式 e^{λx} ≤ 1 + λx + x²(e^λ − 1 − λ)（经
g(x) = (e^{λx}−1−λx)/x² 的单调性），本文件未证明；完整的鞅差序列
Bernstein（条件方差）见 RealAzuma 的独立差版本与后续工作说明。 -/

end Lattice
