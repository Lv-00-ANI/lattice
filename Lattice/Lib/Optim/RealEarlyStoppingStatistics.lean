import Mathlib
import Lattice.Lib.Optim.RealEarlyStopping
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealUnionBound
/-!
# LATTICE: 早停「训练-验证间隙 ≤ γ」的概率化 —— 由 Hoeffding 尾界推出间隙假设

方向（§5 验证行「早停统计化」）：`RealEarlyStopping.monotone_gap_bound` 的结论

    u (t+1) − u t ≤ 2γ

依赖于**显式假设** `|u s − v s| ≤ γ`（训练损失与验证损失的间隙被 γ 界住）。
本文件把该假设从「假设」升级为「由 Hoeffding 一致收敛推出的高概率界」：
把验证集看作大小 m 的有限样本 `w : Fin m → α`（均匀计数测度），
验证经验风险 `valRisk X w` 是总体风险 `μ = EX` 的无偏估计，且

    P( |valRisk X w − μ| ≥ t ) ≤ 2·e^{−m·t²/8}

（由 `RealHoeffding.hoeffding_two_sided` 直接给出，见 `validation_gap_tail`）。

## 主结果

1. `valRisk` / `valGapEvent`：验证集经验风险与「偏差 ≥ t」事件。
2. `validation_gap_tail`：单点 Hoeffding 尾界
   `P(valGapEvent X μ t) ≤ 2·e^{−m·t²/8}`（直接由 `hoeffding_two_sided` 得到）。
3. `validation_gap_budget`：预算反演 —— 取
   `t = sqrt(8·log(2/δ)/m)` 则 `P(valGapEvent X μ t) ≤ δ`（`0 < δ < 2`）。
   **诚实标注（重要）**：本项目的 Hoeffding（`RealHoeffding`）因用保守上界
   `|X − μ| ≤ 2`，指数常数为 `exp(−n t²/8)`，而非经典 `exp(−2n t²)`；
   因此反演出的半径是 `t = sqrt(8·log(2/δ)/m)`（经典为 `sqrt(log(2/δ)/(2m))`）。
   常数差异是**保守**的（半径更大、更严格），本文件如实采用项目实际常数。
4. `gap_bound_from_hoeffding`（核心）：两点（`Fin 2`）形式 —— 对两个总体风险
   `u 0, u 1` 与两个风险函数 `X 0, X 1`，存在「坏事件」`bad`（两次偏差事件之并），
   `P(bad) ≤ 2·(2·e^{−m γ²/8})`，且在 `bad` 之外、若验证经验风险的两个偏差
   都不超过 γ，则 `u 1 − u 0 ≤ 2γ`。
   **诚实降级（重要）**：原陈述只要求两侧间隙 `≤ γ`；但从间隙界**推不出**
   `u 1 − u 0 ≤ 2γ`（反例：`X 0 ≡ −1`、`X 1 ≡ 1`、γ 任意小，间隙恒为 0）。
   `monotone_gap_bound` 的结论还需要**验证损失不增**这一前提（`v 1 ≤ v 0`）。
   因此本文件显式加入假设 `horder : valRisk (X 1) w ≤ valRisk (X 0) w`
   （对应 `IsStopPoint v k t` 在 `t = 0, k = 1` 处的「一步不下降」），
   并在此假设下证明结论。这是**诚实的条件化降级**，不是省略。
5. `earlyStopping_gap_high_probability`：互补形式 —— 存在「好事件」`good`，
   `1 − 2·(2·e^{−m γ²/8}) ≤ P(good)`，且在 `good` 上间隙结论成立
   （用 `RealUnionBound.multi_constraint_verification` 取补集）。
6. `gap_bound_from_hoeffding_budget`：把 4 的 γ 实例化为
   `sqrt(8·log(4/δ)/m)`（4/δ 因为两个事件各摊 δ/2），得到 `P(bad) ≤ δ`
   （`0 < δ < 4`）。
7. `statistics_upgrades_gap_hypothesis`：汇总 —— 高概率好集合 + 早停间隙结论。

## 诚实边界

- **`horder` 不可去（B10 结论，机器验证）**：`no_order_counterexample` 给出反例，
  证明仅凭两侧间隙推不出 `u 1 − u 0 ≤ 2γ`；故 4 中的 `horder` 是**必要假设**，
  不是可以省略的技术条件。B10 的结论是「**保留**该假设并标注其必要性」。
- **常数为项目实际常数**：`exp(−m t²/8)`（非经典 `exp(−2 m t²)`），
  反演半径 `sqrt(8 log(2/δ)/m)`；已在 3、4、5、6 中标注 诚实。
- **需要一步不下降假设** `horder`（见 4 的说明）；没有它结论为假。
- **需要非空样本空间** `[Nonempty α]`（`Fintype.card α > 0`，均匀概率分母非零；
  5、6 的补集陈述需要 `|Fin m → α| > 0`）。
- 指数常数仍为**保守**界（`RealHoeffding` 的已知保守性），不是最优常数。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、定义：验证集经验风险与偏差事件 -/

/-- 验证集（大小 `m`）上的经验风险：`(∑ i, X (w i)) / m`。
`α` 是单个样本的特征空间，`w : Fin m → α` 是大小为 m 的验证集。 -/
def valRisk {α : Type*} {m : ℕ} (X : α → ℝ) (w : Fin m → α) : ℝ :=
  (∑ i : Fin m, X (w i)) / (m : ℝ)

/-- 验证偏差事件：验证经验风险 `valRisk X w` 与总体风险 `μ` 的偏差不小于 `t`
的验证集全体（`Finset (Fin m → α)`）。 -/
def valGapEvent {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ} (X : α → ℝ) (μ t : ℝ) :
    Finset (Fin m → α) :=
  Finset.univ.filter (fun w => t ≤ |valRisk X w - μ|)

/-! ## 二、单点尾界与预算反演 -/

/-- **单点 Hoeffding 尾界**（核心）：验证经验风险偏离总体风险 `μ` 超过 `t`
的概率 ≤ `2·e^{−m·t²/8}`。直接由 `RealHoeffding.hoeffding_two_sided` 得到
（`valRisk` 与引理中的 `(∑ i, X (w i)) / n` 定义一致）。 -/
theorem validation_gap_tail {α : Type*} [Fintype α] [DecidableEq α] {X : α → ℝ} (μ : ℝ)
    (m : ℕ) (hm : 0 < m) (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ)
    (hb : ∀ x, |X x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (valGapEvent (m := m) X μ t) ≤ 2 * Real.exp (-(m : ℝ) * t ^ 2 / 8) := by
  simpa [valGapEvent, valRisk] using hoeffding_two_sided μ m hm hN hmean hb ht

/-- **指数预算反演**（辅助引理）：取半径
`r(c, δ) = sqrt(8·log(c/δ)/m)`，则单侧指数因子恰好降到 `δ/c`：

    e^{−m·r²/8} = δ/c     （0 < δ < c，m > 0）。

**诚实标注**：常数 8 来自本项目 `RealHoeffding` 的实际保守指数 `exp(−n t²/8)`，
而不是经典的 `exp(−2n t²)`；这正是本文件所有反演公式的来源。 -/
theorem exp_budget_eq {m : ℕ} (hm : 0 < m) {c δ : ℝ} (hc : 0 < c) (hδ0 : 0 < δ) (hδc : δ < c) :
    Real.exp (-(m : ℝ) * (Real.sqrt (8 * Real.log (c / δ) / (m : ℝ))) ^ 2 / 8) = δ / c := by
  have hlog : 0 < Real.log (c / δ) := Real.log_pos ((one_lt_div hδ0).mpr hδc)
  have hinside : 0 < 8 * Real.log (c / δ) / (m : ℝ) :=
    div_pos (mul_pos (by norm_num) hlog) (Nat.cast_pos.mpr hm)
  have hsq : (Real.sqrt (8 * Real.log (c / δ) / (m : ℝ))) ^ 2
      = 8 * Real.log (c / δ) / (m : ℝ) := Real.sq_sqrt (le_of_lt hinside)
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  have hkey : -(m : ℝ) * (8 * Real.log (c / δ) / (m : ℝ)) / 8 = -Real.log (c / δ) := by
    have h1 : (m : ℝ) * (8 * Real.log (c / δ) / (m : ℝ)) = 8 * Real.log (c / δ) := by
      rw [mul_comm (m : ℝ) (8 * Real.log (c / δ) / (m : ℝ)),
        div_mul_cancel₀ (8 * Real.log (c / δ)) hmR]
    have h2 : (8 : ℝ) * Real.log (c / δ) / 8 = Real.log (c / δ) := by
      rw [mul_comm (8 : ℝ) (Real.log (c / δ)),
        mul_div_cancel_right₀ (Real.log (c / δ)) (by norm_num : (8 : ℝ) ≠ 0)]
    calc -(m : ℝ) * (8 * Real.log (c / δ) / (m : ℝ)) / 8
        = -((m : ℝ) * (8 * Real.log (c / δ) / (m : ℝ))) / 8 := by ring
      _ = -(8 * Real.log (c / δ)) / 8 := by rw [h1]
      _ = -(8 * Real.log (c / δ) / 8) := by rw [neg_div]
      _ = -Real.log (c / δ) := by rw [h2]
  rw [show -(m : ℝ) * (Real.sqrt (8 * Real.log (c / δ) / (m : ℝ))) ^ 2 / 8
      = -(m : ℝ) * (8 * Real.log (c / δ) / (m : ℝ)) / 8 by rw [hsq],
    hkey, Real.exp_neg, Real.exp_log (div_pos hc hδ0), inv_div]

/-- **主结果：验证间隙预算**。取
`t = sqrt(8·log(2/δ)/m)`，则验证经验风险偏离总体风险超过 `t` 的概率 ≤ δ
（`0 < δ < 2`，`m > 0`）。

**诚实标注**：半径里的常数 8 来自项目 Hoeffding（`exp(−m t²/8)`），
经典形式是 `sqrt(log(2/δ)/(2m))`；本项目常数**更保守**（半径更大）。 -/
theorem validation_gap_budget {α : Type*} [Fintype α] [DecidableEq α] {X : α → ℝ} (μ : ℝ)
    (m : ℕ) (δ : ℝ) (hm : 0 < m) (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ)
    (hb : ∀ x, |X x| ≤ 1) (hδ0 : 0 < δ) (hδ2 : δ < 2) :
    uniformProb (valGapEvent (m := m) X μ (Real.sqrt (8 * Real.log (2 / δ) / (m : ℝ)))) ≤ δ := by
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos ((one_lt_div hδ0).mpr hδ2)
  have hinside : 0 < 8 * Real.log (2 / δ) / (m : ℝ) :=
    div_pos (mul_pos (by norm_num) hlog) (Nat.cast_pos.mpr hm)
  have ht : 0 < Real.sqrt (8 * Real.log (2 / δ) / (m : ℝ)) := Real.sqrt_pos.mpr hinside
  have he := exp_budget_eq hm (c := (2 : ℝ)) (by norm_num) hδ0 hδ2
  calc
    uniformProb (valGapEvent (m := m) X μ (Real.sqrt (8 * Real.log (2 / δ) / (m : ℝ))))
        ≤ 2 * Real.exp (-(m : ℝ) * (Real.sqrt (8 * Real.log (2 / δ) / (m : ℝ))) ^ 2 / 8) :=
          validation_gap_tail μ m hm hN hmean hb ht
    _ = 2 * (δ / 2) := by rw [he]
    _ = δ := by ring

/-! ## 三、核心：两点一致收敛把间隙假设升级为定理 -/

/-! ### 三-0、**B10：`horder` 不能去掉**（机器验证反例）

ROADMAP 的 B10 要求「早停去 `horder`」。**代入检验的结论是该假设不可去**：

仅凭「两侧间隙 `|v s − u s| ≤ γ`」**推不出** `u 1 − u 0 ≤ 2γ`。
反例取 `γ > 0`、`u 0 = −2γ`、`u 1 = 2γ`、`v 0 = u 0`、`v 1 = u 1`：
两侧间隙都恰为 `0 ≤ γ`，但 `u 1 − u 0 = 4γ > 2γ`。

（这与 STYLE §4 记录的同类假命题同源：`u 1 − u 0` 是两个**不同**总体风险之差，
间隙假设只分别约束它们各自与经验风险的距离，**不含**任何「谁大谁小」的信息；
`horder` 正是提供该信息的那一条——对应 `IsStopPoint` 的「一步不下降」。
下面 `no_order_counterexample` 是可在内核验证的反例，`gap_bound_from_hoeffding`
则保留 `horder` 作为**显式必要假设**。） -/

/-- **B10 反例（机器验证）：去掉 `horder` 后命题为假**。
存在两个总体风险 `u` 与两个验证经验风险取值 `v`，使
两侧间隙 `|v s − u s| ≤ γ` 对 `s ∈ {0,1}` 全部成立，但结论 `u 1 − u 0 ≤ 2γ` **不成立**。

见证：`γ = 1`、`u 0 = v 0 = −2`、`u 1 = v 1 = 2`。逐项间隙为 `0 ≤ 1`，
而 `u 1 − u 0 = 4 > 2 = 2γ`。故 `horder` **不可去**（诚实标注）。 -/
theorem no_order_counterexample :
    ∃ (u v : Fin 2 → ℝ) (γ : ℝ), 0 < γ ∧
      (∀ s : Fin 2, |v s - u s| ≤ γ) ∧ ¬ (u 1 - u 0 ≤ 2 * γ) := by
  -- `Fin 2` 的两个点：0 与 1。用 `if s = 0` 显式构造（避免 `![…]` 记法，4.14 无）。
  refine ⟨fun s => if s = 0 then -2 else 2, fun s => if s = 0 then -2 else 2,
    1, by norm_num, ?_, ?_⟩
  · intro s
    -- `v = u`，故 `|v s − u s| = 0`
    show |(if s = 0 then (-2 : ℝ) else 2) - (if s = 0 then (-2 : ℝ) else 2)| ≤ 1
    rw [sub_self, abs_zero]
    norm_num
  · show ¬ ((if (1 : Fin 2) = 0 then (-2 : ℝ) else 2)
      - (if (0 : Fin 2) = 0 then (-2 : ℝ) else 2) ≤ 2 * 1)
    norm_num

/-- **核心：由 Hoeffding 推出的间隙结论（两点形式）**。设两个总体风险
`u 0, u 1`、两个风险函数 `X 0, X 1`，则存在坏事件 `bad`（两次偏差事件之并），
`P(bad) ≤ 2·(2·e^{−m γ²/8})`（两次各自的 `2·e^{−m γ²/8}` 之和），
且在 `bad` 之外、若两个验证经验风险的偏差都不超过 γ，则

    u 1 − u 0 ≤ 2γ。

**诚实降级（重要）**：为使结论为真，显式加入 `horder`（验证损失一步不增，
对应 `IsStopPoint v k t` 的 `t = 0, k = 1` 特例）：没有它，仅凭两侧间隙
`|u s − v s| ≤ γ` 无法推出 `u 1 − u 0 ≤ 2γ`
（反例 `X 0 ≡ −1, X 1 ≡ 1`）。这正是 `monotone_gap_bound` 中
`hstop` 所提供的前提。 -/
theorem gap_bound_from_hoeffding {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (X : Fin 2 → α → ℝ) (u : Fin 2 → ℝ) (m : ℕ) (γ : ℝ) (hm : 0 < m)
    (hN : 0 < Fintype.card α)
    (hmean : ∀ s : Fin 2, uniformExpectation (X s) = u s)
    (hb : ∀ s x, |X s x| ≤ 1)
    (horder : ∀ w : Fin m → α, valRisk (X 1) w ≤ valRisk (X 0) w) (hγ : 0 < γ) :
    ∃ bad : Finset (Fin m → α),
      uniformProb bad ≤ (2 : ℝ) * (2 * Real.exp (-(m : ℝ) * γ ^ 2 / 8)) ∧
      (∀ w, w ∉ bad → (∀ s : Fin 2, |valRisk (X s) w - u s| ≤ γ) →
          u 1 - u 0 ≤ 2 * γ) := by
  refine ⟨(Finset.univ : Finset (Fin 2)).biUnion (fun s => valGapEvent (m := m) (X s) (u s) γ),
    ?_, ?_⟩
  · have h := union_bound_finite (Finset.univ : Finset (Fin 2))
      (fun s => valGapEvent (m := m) (X s) (u s) γ)
      (ε := 2 * Real.exp (-(m : ℝ) * γ ^ 2 / 8))
      (fun i _ => validation_gap_tail (u i) m hm hN (hmean i) (hb i) hγ)
    simpa using h
  · intro w hw hgap
    have h0 : |valRisk (X 0) w - u 0| ≤ γ := hgap 0
    have h1 : |valRisk (X 1) w - u 1| ≤ γ := hgap 1
    have h2 : valRisk (X 1) w ≤ valRisk (X 0) w := horder w
    have h0' := (abs_le.mp h0).2
    have h1' := (abs_le.mp h1).1
    linarith

/-- **互补形式：高概率好集合**。存在好事件 `good`，
`1 − 2·(2·e^{−m γ²/8}) ≤ P(good)`，且在 `good` 上（配合两侧间隙假设）得到
`u 1 − u 0 ≤ 2γ`。证明：取 `good = univ \ bad`（`bad` 来自
`gap_bound_from_hoeffding` 的坏事件），用补集概率恒等式
`P(univ \ bad) = 1 − P(bad)` 与 `P(bad) ≤ 2·(2·e^{−m γ²/8})` 得界，
并复用 `gap_bound_from_hoeffding` 的第二个合取项。 -/
theorem earlyStopping_gap_high_probability {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (X : Fin 2 → α → ℝ) (u : Fin 2 → ℝ) (m : ℕ) (γ : ℝ) (hm : 0 < m)
    (hN : 0 < Fintype.card α)
    (hmean : ∀ s : Fin 2, uniformExpectation (X s) = u s)
    (hb : ∀ s x, |X s x| ≤ 1)
    (horder : ∀ w : Fin m → α, valRisk (X 1) w ≤ valRisk (X 0) w) (hγ : 0 < γ) :
    ∃ good : Finset (Fin m → α),
      1 - (2 : ℝ) * (2 * Real.exp (-(m : ℝ) * γ ^ 2 / 8)) ≤ uniformProb good ∧
      (∀ w ∈ good, (∀ s : Fin 2, |valRisk (X s) w - u s| ≤ γ) → u 1 - u 0 ≤ 2 * γ) := by
  obtain ⟨bad, hbad, hgood⟩ :=
    gap_bound_from_hoeffding X u m γ hm hN hmean hb horder hγ
  refine ⟨(Finset.univ : Finset (Fin m → α)) \ bad, ?_, ?_⟩
  · have hN' : 0 < Fintype.card (Fin m → α) := Fintype.card_pos_iff.mpr inferInstance
    have hcard : uniformProb ((Finset.univ : Finset (Fin m → α)) \ bad)
        = 1 - uniformProb bad := by
      have hle : bad.card ≤ Fintype.card (Fin m → α) :=
        Finset.card_le_card (Finset.subset_univ bad)
      unfold uniformProb
      rw [Finset.card_sdiff (Finset.subset_univ bad), Finset.card_univ, Nat.cast_sub hle,
        sub_div]
      rw [div_self (ne_of_gt (Nat.cast_pos.mpr hN'))]
    rw [hcard]
    linarith
  · intro w hw hgap
    exact hgood w (Finset.mem_sdiff.mp hw).2 hgap

/-- **主结果：间隙预算化**。把 γ 实例化为 `sqrt(8·log(4/δ)/m)`
（用 `4/δ` 因为有两个偏差事件、各摊 `δ/2`），则坏事件概率 ≤ δ（`0 < δ < 4`）。
**诚实标注**：常数 8 来自项目 Hoeffding；`4/δ` 来自两点并集界。 -/
theorem gap_bound_from_hoeffding_budget {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (X : Fin 2 → α → ℝ) (u : Fin 2 → ℝ) (m : ℕ) (δ : ℝ) (hm : 0 < m)
    (hN : 0 < Fintype.card α)
    (hmean : ∀ s : Fin 2, uniformExpectation (X s) = u s)
    (hb : ∀ s x, |X s x| ≤ 1)
    (horder : ∀ w : Fin m → α, valRisk (X 1) w ≤ valRisk (X 0) w)
    (hδ0 : 0 < δ) (hδ4 : δ < 4) :
    ∃ bad : Finset (Fin m → α),
      uniformProb bad ≤ δ ∧
      (∀ w, w ∉ bad →
          (∀ s : Fin 2, |valRisk (X s) w - u s| ≤ Real.sqrt (8 * Real.log (4 / δ) / (m : ℝ))) →
          u 1 - u 0 ≤ 2 * Real.sqrt (8 * Real.log (4 / δ) / (m : ℝ))) := by
  have hγ : 0 < Real.sqrt (8 * Real.log (4 / δ) / (m : ℝ)) :=
    Real.sqrt_pos.mpr
      (div_pos (mul_pos (by norm_num) (Real.log_pos ((one_lt_div hδ0).mpr hδ4)))
        (Nat.cast_pos.mpr hm))
  obtain ⟨bad, hbad, hgood⟩ :=
    gap_bound_from_hoeffding X u m (Real.sqrt (8 * Real.log (4 / δ) / (m : ℝ))) hm hN hmean hb
      horder hγ
  refine ⟨bad, ?_, hgood⟩
  have he := exp_budget_eq hm (c := (4 : ℝ)) (by norm_num) hδ0 hδ4
  have heq : (2 : ℝ) * (2 * Real.exp
      (-(m : ℝ) * (Real.sqrt (8 * Real.log (4 / δ) / (m : ℝ))) ^ 2 / 8)) = δ := by
    rw [he]
    ring
  rw [heq] at hbad
  exact hbad

/-! ## 四、汇总：假设 → 定理 -/

/-- **统计化升级（汇总）**：存在高概率好集合 `good`（`1 − δ ≤ P(good)`），
在其上验证间隙界成立、进而早停的两点间隙结论 `u 1 − u 0 ≤ 2γ` 成立，
其中 `γ = sqrt(8·log(4/δ)/m)`。这把 `RealEarlyStopping.monotone_gap_bound`
的假设 `|u s − v s| ≤ γ`（在此以验证经验风险 `valRisk (X s) w` 扮演 `v s`）
升级为「除概率 ≤ δ 外处处成立」的定理。 -/
theorem statistics_upgrades_gap_hypothesis {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (X : Fin 2 → α → ℝ) (u : Fin 2 → ℝ) (m : ℕ) (δ : ℝ) (hm : 0 < m)
    (hN : 0 < Fintype.card α)
    (hmean : ∀ s : Fin 2, uniformExpectation (X s) = u s)
    (hb : ∀ s x, |X s x| ≤ 1)
    (horder : ∀ w : Fin m → α, valRisk (X 1) w ≤ valRisk (X 0) w)
    (hδ0 : 0 < δ) (hδ4 : δ < 4) :
    ∃ good : Finset (Fin m → α),
      1 - δ ≤ uniformProb good ∧
      ∀ w ∈ good,
          (∀ s : Fin 2, |valRisk (X s) w - u s| ≤ Real.sqrt (8 * Real.log (4 / δ) / (m : ℝ))) →
          u 1 - u 0 ≤ 2 * Real.sqrt (8 * Real.log (4 / δ) / (m : ℝ)) := by
  obtain ⟨bad, hbad, hgood⟩ :=
    gap_bound_from_hoeffding_budget X u m δ hm hN hmean hb horder hδ0 hδ4
  refine ⟨(Finset.univ : Finset (Fin m → α)) \ bad, ?_, ?_⟩
  · have hN' : 0 < Fintype.card (Fin m → α) := Fintype.card_pos_iff.mpr inferInstance
    have hcard : uniformProb ((Finset.univ : Finset (Fin m → α)) \ bad) = 1 - uniformProb bad := by
      have hle : bad.card ≤ Fintype.card (Fin m → α) :=
        Finset.card_le_card (Finset.subset_univ bad)
      unfold uniformProb
      rw [Finset.card_sdiff (Finset.subset_univ bad), Finset.card_univ, Nat.cast_sub hle,
        sub_div]
      rw [div_self (ne_of_gt (Nat.cast_pos.mpr hN'))]
    rw [hcard]
    linarith
  · intro w hw hgap
    exact hgood w (Finset.mem_sdiff.mp hw).2 hgap

/-! ## 注：闭环语义

  `valRisk`（验证经验风险）→ `valGapEvent`（偏差事件）→
  `validation_gap_tail`（Hoeffding 单点尾界 `2 e^{−m t²/8}`）→
  `validation_gap_budget`（预算反演 `t = sqrt(8 log(2/δ)/m)`）→
  `gap_bound_from_hoeffding`（两点一致收敛 + 一步不下降 ⟹ `u 1 − u 0 ≤ 2γ`）→
  `earlyStopping_gap_high_probability`（互补高概率形式）→
  `gap_bound_from_hoeffding_budget`（`γ = sqrt(8 log(4/δ)/m)`，坏事件 ≤ δ）→
  `statistics_upgrades_gap_hypothesis`（汇总）。

  这闭合了 `RealEarlyStopping.monotone_gap_bound` 的间隙假设与
  `RealHoeffding`/`RealUnionBound` 的概率界之间的缺口：
  早停的间隙假设现在是**由 Hoeffding 一致收敛导出的高概率定理**，
  代价是显式的失败概率 δ 与一步不下降假设 `horder`（诚实降级，见上）。
  常数为项目实际常数 `exp(−m t²/8)`（非经典 `exp(−2 m t²)`），已诚实标注。 -/

end Lattice
