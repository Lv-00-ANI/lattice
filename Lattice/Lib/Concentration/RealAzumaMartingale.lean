import Mathlib
import Lattice.Lib.Concentration.RealAzuma
import Lattice.Lib.Concentration.RealStochasticProcess
/-!
# LATTICE: 真鞅版 Azuma —— 条件 Hoeffding 步 + 塔性质链 + 尾界

RealAzuma 在 docstring（第 20–29 行）中**明确声明**它做的是「独立有界差」特例，
**未**做完整鞅版：完整 Azuma 的关键缺失步骤是**条件 Hoeffding 引理**
「`E[Dᵢ | F_{i−1}] = 0`、`|Dᵢ| ≤ cᵢ` ⟹ `E[e^{λDᵢ} | F_{i−1}] ≤ e^{λ²cᵢ²/2}`」
以及把它沿滤链**串成乘积**的塔性质步骤。本文件用 RealStochasticProcess 的
有限纤维条件期望补上这两个步骤。

定理链：
  1. `condExpFiber_eq_uniformExpectation`（**桥接**）：非空纤维上，纤维均值条件期望
     = 该纤维子类型上的 `uniformExpectation`（`Finset.sum_subtype` + `Fintype.card_coe`）。
  2. `condExpFiber_hoeffding`（**条件 Hoeffding，核心**）：若鞅差 `d` 的纤维均值为零
     （`CondZeroMean`）、`|d| ≤ c`、`c > 0`、所有纤维非空，则对任意 `b`
     `E[e^{λd} | π](b) ≤ exp(λ²c²/2)`。
     证明：桥接定理把左端化为纤维子类型上的均匀期望，直接调用
     `RealAzuma.hoeffding_lemma_scaled`（|X| ≤ c、EX = 0 ⟹ E[e^{λX}] ≤ e^{λ²c²/2}）。
  3. `FibreBound`（def）：纤维上条件期望一致上界 `∀ b, E[Y|π](b) ≤ EB`。
  4. `fiberCard_sum_eq`：`∑_{b : g b = c} |细纤维 b| = |粗纤维 c|`（取 `X = 1` 的
     `fiber_sum_eq_filtered_fiber_sum`）。
  5. `weightedCondExp_le_mul`：若 `E[Y|π] ≤ EB` 逐纤维成立，则加权聚合
     `weightedCondExp π g Y c ≤ |粗纤维 c| · EB`。
  6. `tower_hoeffding_transfer`（**塔性质链，核心**）：把条件 MGF 界从**细滤链**
     `π` 提升到**粗滤链** `g ∘ π`：`E[Y|细] ≤ EB`（逐纤维）⟹ `E[Y|粗] ≤ EB`。
     证明：`tower_property`（RealStochasticProcess）给出
     `|粗|·E[Y|粗] = ∑_{b:g b=c} |细 b|·E[Y|细](b)`，用定理 4、5 两边夹出
     `|粗|·E[Y|粗] ≤ |粗|·EB`，再除以正基数 `|粗|`。**这正是完整鞅版 Azuma
     沿滤链串接所需的步骤**（把逐步条件界合成为整段的界）。
  7. `uniformExpectation_exp_le_of_condZeroMean`（**无条件 MGF 界**）：条件零均值 +
     有界 ⟹ **全空间**均匀期望满足 `E[e^{λd}] ≤ exp(λ²c²/2)`。
     证明：`∑_a e^{λd} = ∑_b |纤维 b|·E[e^{λd}|π](b) ≤ (∑_b |纤维 b|)·exp(λ²c²/2)
     = N·exp(λ²c²/2)`，除以 `N`。
  8. `azuma_tail_of_mgf`：由 MGF 界 `E[e^{λS}] ≤ exp(λ²σ²/2)` 经切尔诺夫马尔可夫桥
     `RealHoeffding.markov_exp_tail` 得 `P(S ≥ t) ≤ exp(−t²/(2σ²))`（取 `λ = t/σ²`）。
  9. `azuma_tail_martingale`（**鞅版尾界**）：鞅差 + 有界 ⟹
     `P(d ≥ t) ≤ exp(−t²/(2c²))`（7 + 8 复合）。

**诚实假设与降级（重要）**：
- 本文件补齐了 RealAzuma 缺失的**条件 Hoeffding 步（定理 2）**与**塔性质串接步
  （定理 6）**——这两步是「真鞅版」区别于「独立有界差特例」的核心。
- 但**多期滤链的完整迭代**（把定理 6 沿 `n` 期滤链逐步复合，得到
  `E[e^{λ∑Dᵢ}] ≤ exp(λ²∑cᵢ²/2)`）本文件**未做**：它需要在 `n` 期嵌套投影
  `π₀ ⊑ π₁ ⊑ ⋯` 上做归纳，并处理每期投影的索引类型变化（本文件已解决的
  两索引类型共存问题只覆盖单步）。定理 6 给出**单步长链的完整证明**，
  多步迭代如实标注为剩余工作。
- 定理 9 的尾界针对**单个**有界鞅差 `d`（即单步 Azuma / Hoeffding 的鞅版本），
  而非 `n` 项和；多项和的情形由 RealAzuma 的独立版本给出（其常数精确）。
- 均匀（计数）概率空间 + 纤维均值条件期望（有限版），非全测度论 `condexp`。

**#check 结果（mathlib 4.14 实测）**：`Finset.sum_subtype :
  (∀ x, x ∈ s ↔ p x) → ∑ a ∈ s, f a = ∑ a : Subtype p, f ↑a`；
`Fintype.card_coe (s : Finset α) : Fintype.card {x // x ∈ s} = s.card`；
`Finset.sum_filter`、`Real.exp_sum`、`ProbabilityTheory.measure_ge_le_exp_mul_mgf`
（同类测度论版本见 RealHoeffdingMeasure）。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {α β γ : Type*} [Fintype α] [DecidableEq β]

/-! ## 一、纤维均值 = 纤维子类型上的均匀期望（桥接） -/

/-- **桥接**：非空纤维上，纤维均值条件期望 = 该纤维子类型上的 `uniformExpectation`。 -/
theorem condExpFiber_eq_uniformExpectation (π : α → β) (X : α → ℝ) (b : β)
    (h : (fiber π b).card ≠ 0) :
    condExpFiber π X b = uniformExpectation (fun a : {a // a ∈ fiber π b} => X a.1) := by
  classical
  have hcard : Fintype.card {a // a ∈ fiber π b} = (fiber π b).card := Fintype.card_coe _
  have hsum : (∑ a : {a // a ∈ fiber π b}, X a.1) = ∑ a in fiber π b, X a :=
    (Finset.sum_subtype (fiber π b) (fun x => Iff.rfl) X).symm
  rw [condExpFiber, if_neg h, uniformExpectation, hsum, hcard]

/-! ## 二、条件 Hoeffding 引理（核心：鞅差的有界性 ⟹ 条件 MGF 界） -/

/-- **条件 Hoeffding（核心）**：鞅差（纤维均值零）+ `|d| ≤ c` + `c > 0` + 纤维非空
⟹ 每个纤维上的条件 MGF ≤ `exp(λ²c²/2)`。证明：桥接定理 + `hoeffding_lemma_scaled`。 -/
theorem condExpFiber_hoeffding (π : α → β) (d : α → ℝ) {c lam : ℝ}
    (hzero : CondZeroMean π d) (hc : 0 < c) (hb : ∀ a, |d a| ≤ c)
    (hne : ∀ b, (fiber π b).card ≠ 0) (b : β) :
    condExpFiber π (fun a => Real.exp (lam * d a)) b ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) := by
  classical
  rw [condExpFiber_eq_uniformExpectation π _ b (hne b)]
  refine hoeffding_lemma_scaled (X := fun a : {a // a ∈ fiber π b} => d a.1) ?hN hc ?hzero' ?hb'
  · rw [Fintype.card_coe]
    exact Nat.pos_of_ne_zero (hne b)
  · rw [← Finset.sum_subtype (fiber π b) (fun x => Iff.rfl) d]
    exact hzero b
  · intro a
    exact hb a.1

/-! ## 三、塔性质串接（把条件界从细滤链提升到粗滤链） -/

/-- **纤维一致上界**：`∀ b, E[Y | π](b) ≤ EB`（用 def 包装，避免同一陈述中
两种纤维索引类型的 `condExpFiber` 混用）。 -/
def FibreBound (π : α → β) (Y : α → ℝ) (EB : ℝ) : Prop := ∀ b, condExpFiber π Y b ≤ EB

/-- **纤维基数求和**：`∑_{b : g b = c} |细纤维 b| = |粗纤维 c|`。 -/
theorem fiberCard_sum_eq [Fintype β] (π : α → β) (g : β → γ) [DecidableEq γ] (c : γ) :
    ∑ b in (Finset.univ : Finset β).filter (fun b : β => g b = c), ((fiber π b).card : ℝ)
      = ((fiber (fun a => g (π a)) c).card : ℝ) := by
  have h1 := fiber_sum_eq_filtered_fiber_sum π g (fun _ : α => (1 : ℝ)) c
  simpa [Finset.sum_const, nsmul_eq_mul] using h1.symm

/-- **加权聚合上界**：逐纤维 `E[Y|π] ≤ EB` ⟹ `weightedCondExp π g Y c ≤ |粗纤维 c|·EB`。 -/
theorem weightedCondExp_le_mul [Fintype β] (π : α → β) (g : β → γ) [DecidableEq γ]
    (Y : α → ℝ) {EB : ℝ} (c : γ) (h : ∀ b, condExpFiber π Y b ≤ EB) :
    weightedCondExp π g Y c ≤ ((fiber (fun a => g (π a)) c).card : ℝ) * EB := by
  unfold weightedCondExp
  calc ∑ b in (Finset.univ : Finset β).filter (fun b : β => g b = c),
        ((fiber π b).card : ℝ) * condExpFiber π Y b
      ≤ ∑ b in (Finset.univ : Finset β).filter (fun b : β => g b = c),
        ((fiber π b).card : ℝ) * EB :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (h b) (Nat.cast_nonneg _))
    _ = (∑ b in (Finset.univ : Finset β).filter (fun b : β => g b = c),
        ((fiber π b).card : ℝ)) * EB := by rw [Finset.sum_mul]
    _ = ((fiber (fun a => g (π a)) c).card : ℝ) * EB := by
        rw [fiberCard_sum_eq π g c]

/-- **塔性质串接（核心）**：条件 MGF 界从细滤链 `π` 提升到粗滤链 `g ∘ π`。
证明：`tower_property` 的两边夹 + 正基数消去。这是完整鞅版 Azuma 沿滤链
逐步复合的**单步**。 -/
theorem tower_hoeffding_transfer [Fintype β] (π : α → β) (g : β → γ) [DecidableEq γ]
    (Y : α → ℝ) {EB : ℝ} (hne : ∀ c : γ, (fiber (fun a => g (π a)) c).card ≠ 0)
    (hfin : FibreBound π Y EB) : FibreBound (fun a => g (π a)) Y EB := by
  intro c
  have htower := tower_property π g Y c
  have hle := weightedCondExp_le_mul π g Y c hfin
  have hcard : 0 < (fiber (fun a => g (π a)) c).card := Nat.pos_of_ne_zero (hne c)
  have h1 : ((fiber (fun a => g (π a)) c).card : ℝ)
        * condExpFiber (fun a => g (π a)) Y c
      ≤ ((fiber (fun a => g (π a)) c).card : ℝ) * EB := by
    rw [htower]
    exact hle
  exact le_of_mul_le_mul_left h1 (Nat.cast_pos.mpr hcard)

/-! ## 四、无条件 MGF 界与鞅版尾界 -/

/-- **无条件 MGF 界**：条件零均值 + 有界 ⟹ 全空间均匀期望满足
`E[e^{λd}] ≤ exp(λ²c²/2)`。证明：纤维分解 + 定理 2 + `∑_b |纤维 b| = N`。 -/
theorem uniformExpectation_exp_le_of_condZeroMean [Fintype β] (π : α → β) (d : α → ℝ)
    {c lam : ℝ}
    (hN : 0 < Fintype.card α) (hzero : CondZeroMean π d) (hc : 0 < c)
    (hb : ∀ a, |d a| ≤ c) (hne : ∀ b, (fiber π b).card ≠ 0) :
    uniformExpectation (fun a => Real.exp (lam * d a)) ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) := by
  have hsum_card : ∑ b, ((fiber π b).card : ℝ) = (Fintype.card α : ℝ) := by
    have h := fiber_sum_eq π (fun _ : α => (1 : ℝ))
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hbound : ∑ b, ((fiber π b).card : ℝ)
        * condExpFiber π (fun a => Real.exp (lam * d a)) b
      ≤ ∑ b, ((fiber π b).card : ℝ) * Real.exp (lam ^ 2 * c ^ 2 / 2) :=
    Finset.sum_le_sum (fun b _ =>
      mul_le_mul_of_nonneg_left (condExpFiber_hoeffding π d hzero hc hb hne b) (Nat.cast_nonneg _))
  calc uniformExpectation (fun a => Real.exp (lam * d a))
      = (∑ b, ((fiber π b).card : ℝ)
          * condExpFiber π (fun a => Real.exp (lam * d a)) b) / (Fintype.card α : ℝ) := by
        rw [uniformExpectation]
        congr 1
        rw [← fiber_sum_eq (π := π) (X := fun a => Real.exp (lam * d a))]
        exact Finset.sum_congr rfl
          (fun b _ => (card_mul_condExpFiber π (fun a => Real.exp (lam * d a)) b).symm)
    _ ≤ (∑ b, ((fiber π b).card : ℝ) * Real.exp (lam ^ 2 * c ^ 2 / 2))
          / (Fintype.card α : ℝ) :=
        div_le_div_of_nonneg_right hbound (Nat.cast_nonneg _)
    _ = Real.exp (lam ^ 2 * c ^ 2 / 2) := by
        have hNne : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
        rw [← Finset.sum_mul, hsum_card]
        field_simp

/-- **MGF 界 ⟹ 指数尾界**：取 `λ = t/σ²` 的切尔诺夫桥。 -/
theorem azuma_tail_of_mgf (S : α → ℝ) {σ2 t : ℝ} (hσ2 : 0 < σ2) (ht : 0 < t)
    (hmgf : uniformExpectation (fun w => Real.exp ((t / σ2) * S w))
      ≤ Real.exp ((t / σ2) ^ 2 * σ2 / 2)) :
    uniformProb (Finset.univ.filter (fun w => t ≤ S w)) ≤ Real.exp (-(t ^ 2) / (2 * σ2)) := by
  have hlam : 0 < t / σ2 := div_pos ht hσ2
  have hch := markov_exp_tail S (t := t) (lam := t / σ2) hlam
  have hstep : Real.exp (-(t / σ2) * t)
        * uniformExpectation (fun w => Real.exp ((t / σ2) * S w))
      ≤ Real.exp (-(t / σ2) * t) * Real.exp ((t / σ2) ^ 2 * σ2 / 2) :=
    mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
  have hexp : Real.exp (-(t / σ2) * t) * Real.exp ((t / σ2) ^ 2 * σ2 / 2)
      = Real.exp (-(t ^ 2) / (2 * σ2)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc uniformProb (Finset.univ.filter (fun w => t ≤ S w))
      ≤ Real.exp (-(t / σ2) * t) * uniformExpectation (fun w => Real.exp ((t / σ2) * S w)) := hch
    _ ≤ Real.exp (-(t / σ2) * t) * Real.exp ((t / σ2) ^ 2 * σ2 / 2) := hstep
    _ = Real.exp (-(t ^ 2) / (2 * σ2)) := hexp

/-- **鞅版 Azuma 尾界**：单个有界鞅差 + 条件零均值 ⟹
`P(d ≥ t) ≤ exp(−t²/(2c²))`（定理 7 + 8，取 `σ² = c²`）。 -/
theorem azuma_tail_martingale [Fintype β] (π : α → β) (d : α → ℝ) {c t : ℝ}
    (hN : 0 < Fintype.card α) (hc : 0 < c) (ht : 0 < t) (hzero : CondZeroMean π d)
    (hb : ∀ a, |d a| ≤ c) (hne : ∀ b, (fiber π b).card ≠ 0) :
    uniformProb (Finset.univ.filter (fun w => t ≤ d w)) ≤ Real.exp (-(t ^ 2) / (2 * c ^ 2)) := by
  have hσ2 : 0 < c ^ 2 := pow_pos hc 2
  refine azuma_tail_of_mgf d hσ2 ht ?_
  exact uniformExpectation_exp_le_of_condZeroMean π d hN hzero hc hb hne

end Lattice
