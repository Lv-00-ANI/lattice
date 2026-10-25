import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: Azuma 型鞅差集中 —— 逐坐标不同界 c_i 的有界差之和

方向（§5 验证行「Azuma / 鞅集中」）：RealHoeffding 的 Hoeffding 尾界要求
n 个副本**同分布**（同一个界 |X| ≤ 1、同一个方差/二阶矩上界），常数只
依赖 n。本文件给出**每坐标不同界** c_i 的更一般集中界（Hoeffding–Azuma 的
「独立有界差」形式）：

  n 个独立坐标、第 i 个坐标的差满足 |dᵢ| ≤ cᵢ 且 E[dᵢ] = 0 ⟹
  E[e^{λΣᵢdᵢ}] ≤ exp(λ²Σᵢcᵢ²/2)，
  P(Σᵢdᵢ ≥ t) ≤ exp(−t²/(2Σᵢcᵢ²))。

这把 Hoeffding 的 e^{−nt²/8}（等界 cᵢ = 1 时 e^{−t²/(2n)} 的更弱保守版）
推广为异质界：**界小的坐标对尾界的贡献按 cᵢ² 加权**，Σcᵢ² 替代 n·c²，
在界参差不齐时严格更紧。

**诚实选择（独立有界差版本，非完整鞅版）**：完整 Azuma 不等式的陈述是
「鞅差序列 Dᵢ 关于滤链 Fᵢ 可测、E[Dᵢ | F_{i−1}] = 0、|Dᵢ| ≤ cᵢ ⟹ …」，
其证明需要在**条件期望**下逐条证明「E[e^{λDᵢ} | F_{i−1}] ≤ e^{λ²cᵢ²/2}」
（鞅差版的 Hoeffding 引理，逐纤维的弦上界），再把条件期望串成乘积。
本文件未走这条路（原因见文末「后续工作」），而采用其**特例**：
Dᵢ 只依赖第 i 个坐标、且该坐标上的均匀均值 Σ_a dᵢ(a) = 0
——在有限均匀乘积空间上，「只依赖第 i 个坐标 + 该坐标均值零」正是
「给定其它坐标的条件期望为零」（独立性 + 均值零），故本文件给出的
是**独立有界差**（即 Hoeffding 的异质界形式）的完整证明，常数精确
（λ²Σcᵢ²/2，无额外损失；对比 RealBernstein 的保守常数）。

**定理链**：
1. `hoeffding_lemma_scaled`：|X| ≤ c、EX = 0、c > 0 ⟹
   E[e^{λX}] ≤ e^{λ²c²/2}。证明：对 Z = X/c 用 `hoeffding_lemma`
   （RealHoeffding，|Z| ≤ 1、EZ = 0 ⟹ E[e^{λZ}] ≤ e^{λ²/2}）取 λ ↦ λc 缩放。
2. `azuma_diff_bound`（核心 MGF 界）：对每坐标 i 给定差函数 dᵢ : α → ℝ
   （|dᵢ(a)| ≤ cᵢ、Σ_a dᵢ(a) = 0），
   E[e^{λΣᵢ dᵢ(Xᵢ)}] = ∏ᵢ E[e^{λdᵢ}] ≤ e^{λ²Σcᵢ²/2}。
   证明：`Real.exp_sum` 把和拆成积，`Finset.prod_univ_sum` 把乘积空间的
   期望分解为各坐标期望之积，逐坐标用定理 1。
3. `azuma_tail`（核心尾界）：P(Σᵢ dᵢ(Xᵢ) ≥ t) ≤ e^{−t²/(2Σcᵢ²)}。
   证明：指数马尔可夫桥 `markov_exp_tail`（RealHoeffding）+ 定理 2，
   取 λ = t/Σcᵢ²：e^{−λt + λ²Σcᵢ²/2} = e^{−t²/(2Σcᵢ²)}。
4. `azuma_tail_uniform`：所有 cᵢ = c 时退化为 e^{−t²/(2nc²)}
   （Hoeffding 的经典形式，本文件常数精确：对比 RealHoeffding 的保守
   e^{−nt²/8} 对应 c = 2 的缩放形式）。
5. `azuma_examples`：具体实例（Rademacher ±1、n = 2、t = 2，界 e^{−1}）。

诚实假设：α 非空（N > 0）、每个 cᵢ > 0、Σcᵢ² > 0（差异非退化）、t > 0。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 引理 1：Hoeffding 引理的缩放版（|X| ≤ c ⟹ E[e^{λX}] ≤ e^{λ²c²/2}）
证明：Z = X/c 满足 |Z| ≤ 1、EZ = 0；`hoeffding_lemma`（RealHoeffding）
给出 E[e^{(λc)Z}] ≤ e^{(λc)²/2}，而 (λc)Z = λX。 -/

theorem hoeffding_lemma_scaled {α : Type*} [Fintype α] {X : α → ℝ} {c lam : ℝ}
    (hN : 0 < Fintype.card α) (hc : 0 < c) (hzero : (∑ x : α, X x) = 0)
    (hb : ∀ x : α, |X x| ≤ c) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) := by
  have hczero : (∑ x : α, X x / c) = 0 := by
    rw [← Finset.sum_div, hzero]
    norm_num
  have hcb : ∀ x : α, |X x / c| ≤ 1 := by
    intro x
    rw [abs_div, abs_of_pos hc]
    exact (div_le_one hc).mpr (hb x)
  have h := hoeffding_lemma (X := fun x => X x / c) (lam := lam * c) hN hczero hcb
  have harg : (fun x : α => Real.exp ((lam * c) * (X x / c)))
      = fun x : α => Real.exp (lam * X x) := by
    funext x
    congr 1
    field_simp [ne_of_gt hc]
    ring
  have h2 : (lam * c) ^ 2 / 2 = lam ^ 2 * c ^ 2 / 2 := by ring
  calc
    uniformExpectation (fun x => Real.exp (lam * X x))
        = uniformExpectation (fun x => Real.exp ((lam * c) * (X x / c))) := by rw [harg]
    _ ≤ Real.exp ((lam * c) ^ 2 / 2) := h
    _ = Real.exp (lam ^ 2 * c ^ 2 / 2) := by rw [h2]

/-! ## 定理 2（核心）：逐坐标不同界的指数矩界（独立有界差）
E[e^{λΣᵢdᵢ(Xᵢ)}] ≤ e^{λ²Σcᵢ²/2}。
证明：`Real.exp_sum`（e^{Σ} = ∏ e^{·}）+ `Finset.prod_univ_sum`
（∏ᵢ∑_a = ∑_w∏ᵢ，即乘积空间期望的乘积分解，独立性）+ 引理 1 逐坐标。 -/

theorem azuma_diff_bound {α : Type*} [Fintype α] (n : ℕ)
    (hN : 0 < Fintype.card α) {d : Fin n → α → ℝ} {c : Fin n → ℝ}
    (hc : ∀ i, 0 < c i) (hd0 : ∀ i, (∑ a : α, d i a) = 0)
    (hdb : ∀ i a, |d i a| ≤ c i) (lam : ℝ) :
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * ∑ i : Fin n, d i (w i))) ≤
      Real.exp (lam ^ 2 * (∑ i : Fin n, (c i) ^ 2) / 2) := by
  have hfunc : (fun w : Fin n → α => Real.exp (lam * (∑ i : Fin n, d i (w i))))
      = fun w : Fin n → α => ∏ i : Fin n, Real.exp (lam * d i (w i)) := by
    funext w
    calc
      Real.exp (lam * (∑ i : Fin n, d i (w i))) = Real.exp (∑ i : Fin n, lam * d i (w i)) := by
        rw [Finset.mul_sum]
      _ = ∏ i : Fin n, Real.exp (lam * d i (w i)) := Real.exp_sum _ _
  calc
    uniformExpectation (fun w : Fin n → α => Real.exp (lam * ∑ i : Fin n, d i (w i)))
        = (∏ i : Fin n, ∑ a : α, Real.exp (lam * d i a)) /
            ((Fintype.card α : ℝ) ^ n) := by
          unfold uniformExpectation
          rw [hfunc]
          rw [Fintype.card_pi_const, Nat.cast_pow]
          congr 1
          rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset α))
            (f := fun i a => Real.exp (lam * d i a))]
          simp
    _ = ∏ i : Fin n, uniformExpectation (fun a => Real.exp (lam * d i a)) := by
          unfold uniformExpectation
          calc
            (∏ i : Fin n, ∑ a : α, Real.exp (lam * d i a)) / ((Fintype.card α : ℝ) ^ n)
                = (∏ i : Fin n, ∑ a : α, Real.exp (lam * d i a)) /
                    (∏ i : Fin n, (Fintype.card α : ℝ)) := by
                  congr 1
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ = ∏ i : Fin n, ((∑ a : α, Real.exp (lam * d i a)) /
                    (Fintype.card α : ℝ)) := by
                  rw [Finset.prod_div_distrib]
    _ ≤ ∏ i : Fin n, Real.exp (lam ^ 2 * (c i) ^ 2 / 2) := by
          apply Finset.prod_le_prod
          · intro i _
            unfold uniformExpectation
            exact div_nonneg (Finset.sum_nonneg (fun a _ => Real.exp_nonneg _))
              (Nat.cast_nonneg _)
          · intro i _
            exact hoeffding_lemma_scaled hN (hc i) (hd0 i) (fun a => hdb i a)
    _ = Real.exp (∑ i : Fin n, lam ^ 2 * (c i) ^ 2 / 2) := by
          rw [Real.exp_sum]
    _ = Real.exp (lam ^ 2 * (∑ i : Fin n, (c i) ^ 2) / 2) := by
          congr 1
          rw [← Finset.sum_div, Finset.mul_sum]

/-! ## 定理 3（核心）：Azuma 型尾界（异质界）
P(Σᵢ dᵢ(Xᵢ) ≥ t) ≤ e^{−t²/(2Σᵢcᵢ²)}。
证明：指数马尔可夫桥 + 定理 2，λ = t/Σcᵢ²。 -/

theorem azuma_tail {α : Type*} [Fintype α] (n : ℕ)
    (hN : 0 < Fintype.card α) {d : Fin n → α → ℝ} {c : Fin n → ℝ}
    (hc : ∀ i, 0 < c i) (hd0 : ∀ i, (∑ a : α, d i a) = 0)
    (hdb : ∀ i a, |d i a| ≤ c i) {t : ℝ} (ht : 0 < t)
    (hS : 0 < ∑ i : Fin n, (c i) ^ 2) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, d i (w i))) ≤
      Real.exp (-t ^ 2 / (2 * ∑ i : Fin n, (c i) ^ 2)) := by
  let S : (Fin n → α) → ℝ := fun w => ∑ i : Fin n, d i (w i)
  let S2 : ℝ := ∑ i : Fin n, (c i) ^ 2
  let lam : ℝ := t / S2
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos ht hS
  have hmgf : uniformExpectation (fun w => Real.exp (lam * S w)) ≤
      Real.exp (lam ^ 2 * S2 / 2) := by
    simpa [S, S2] using azuma_diff_bound (n := n) hN hc hd0 hdb lam
  have hmarkov := markov_exp_tail (S := S) (t := t) (lam := lam) hlam
  have hexp : -lam * t + lam ^ 2 * S2 / 2 = -t ^ 2 / (2 * S2) := by
    dsimp [lam]
    field_simp
    ring
  calc
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, d i (w i)))
        = uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ S w)) := by simp [S]
    _ ≤ Real.exp (-lam * t) * uniformExpectation (fun w => Real.exp (lam * S w)) := hmarkov
    _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * S2 / 2) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp (-lam * t + lam ^ 2 * S2 / 2) := by rw [← Real.exp_add]
    _ = Real.exp (-t ^ 2 / (2 * S2)) := by rw [hexp]
    _ = Real.exp (-t ^ 2 / (2 * ∑ i : Fin n, (c i) ^ 2)) := by rfl

/-! ## 定理 4：等界退化 —— Hoeffding 经典形式
所有 cᵢ = c > 0 ⟹ P(Σᵢ dᵢ(Xᵢ) ≥ t) ≤ e^{−t²/(2nc²)}。
证明：定理 3 中 Σcᵢ² = nc²（`Finset.sum_const` + `Finset.card_univ`）。 -/

theorem azuma_tail_uniform {α : Type*} [Fintype α] (n : ℕ) (hn : 0 < n)
    (hN : 0 < Fintype.card α) {d : Fin n → α → ℝ} {c : ℝ}
    (hc : 0 < c) (hd0 : ∀ i, (∑ a : α, d i a) = 0)
    (hdb : ∀ i a, |d i a| ≤ c) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α => t ≤ ∑ i : Fin n, d i (w i))) ≤
      Real.exp (-t ^ 2 / (2 * (n : ℝ) * c ^ 2)) := by
  have hnℝ : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hS : 0 < ∑ i : Fin n, (fun _ : Fin n => c) i ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_pos hnℝ (pow_pos hc 2)
  have h := azuma_tail (n := n) hN (d := d) (c := fun _ : Fin n => c)
    (fun _ => hc) hd0 hdb ht hS
  have hsum : (∑ i : Fin n, (fun _ : Fin n => c) i ^ 2) = (n : ℝ) * c ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at h
  rw [show 2 * ((n : ℝ) * c ^ 2) = 2 * (n : ℝ) * c ^ 2 from by ring] at h
  exact h

/-! ## 定理 5：具体实例（Rademacher ±1、n = 2、t = 2）
α = Fin 2，dᵢ(a) = (a = 0 ? 1 : −1)（Σ_a dᵢ = 0、|dᵢ| ≤ 1）；n = 2、t = 2
给出 P(Σ ≥ 2) ≤ e^{−4/(2·2·1)} = e^{−1}（真实概率 1/4，界成立）。 -/

/-- Rademacher 型 ±1 差（Fin 2 上的零均值有界函数）。 -/
def azumaRademacher : Fin 2 → ℝ := fun a => if a = 0 then 1 else -1

lemma azumaRademacher_sum_zero : (∑ a : Fin 2, azumaRademacher a) = 0 := by
  rw [Fin.sum_univ_two]
  norm_num [azumaRademacher]

lemma azumaRademacher_abs_le_one : ∀ a : Fin 2, |azumaRademacher a| ≤ 1 := by
  intro a
  fin_cases a <;> norm_num [azumaRademacher]

/-- 具体实例：Rademacher ±1、n = 2、t = 2 的 Azuma 尾界 e^{−1}。 -/
theorem azuma_examples :
    uniformProb (Finset.univ.filter (fun w : Fin 2 → Fin 2 =>
        2 ≤ ∑ i : Fin 2, azumaRademacher (w i))) ≤ Real.exp (-1) := by
  have h := azuma_tail_uniform (n := 2) (d := fun (_ : Fin 2) a => azumaRademacher a)
    (c := 1) (by norm_num : 0 < 2) (by norm_num : 0 < Fintype.card (Fin 2))
    (by norm_num : (0 : ℝ) < 1) (fun _ => azumaRademacher_sum_zero)
    (fun _ a => azumaRademacher_abs_le_one a) (by norm_num : (0 : ℝ) < 2)
  exact le_trans h (Real.exp_le_exp.mpr (by norm_num))

/-! ## 后续工作（诚实标注）：完整鞅版 Azuma

完整 Azuma 的陈述为：Dᵢ 关于滤链 Fᵢ 可测、E[Dᵢ | F_{i−1}] = 0 逐点成立、
|Dᵢ| ≤ cᵢ ⟹ P(ΣᵢDᵢ ≥ t) ≤ e^{−t²/(2Σcᵢ²)}。证明需要在**条件期望**下证明
逐纤维的 Hoeffding 引理「E[e^{λDᵢ} | F_{i−1}] ≤ e^{λ²cᵢ²/2}」再串乘积。

在有限计数设定中这等价于「坐标 i 的纤维求和为零」，需要把全域求和按
「其它坐标取值」重排（每纤维大小 = |α| 的 N 对 1 映射
`w ↦ Function.update w i a`），本文件未形式化该重排引理，故取
「dᵢ 只依赖第 i 个坐标」的特例——此时条件均值零 ⟺ 该坐标均匀均值零
（Σ_a dᵢ(a) = 0），本文件的 `azuma_diff_bound` / `azuma_tail` 即为
独立有界差版本的完整证明；真正的鞅版（依赖时间相关的自适应差）留作后续。

**与 RealBernstein 的衔接**：`azuma_tail` 是「有界差 + 异质界」的常数精确
版本；加入方差信息（RealBernstein 的 `bernstein_tail`）可进一步用 cᵢ² 的
方差替代，二者都是 RealSamplingBoost 多轮验证置信度的单轮界输入。 -/

end Lattice
