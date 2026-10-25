import Mathlib
import Lattice.Lib.LearningTheory.RealSamplingBoost
import Lattice.Lift.RealRandomVerify
/-!
# LATTICE: 并集界（Boole 不等式）与多重验证 —— P(⋃ Aᵢ) ≤ Σ P(Aᵢ)

方向（§5 验证行「多重约束验证」）：`RealRandomVerify` / `RealSamplingBoost`
只给出**单个**约束/事件违背的概率界（单轮 miss ≤ ε、k 轮放大到 ε^k）。
当验证器要同时检查 **k 个约束**时，需要把「至少一个违反」的概率用各约束的
概率上界控制住——这正是 **并集界（union bound / Boole 不等式）**：

  P(A₁ ∪ … ∪ A_k) ≤ P(A₁) + … + P(A_k)

本文件给出：

  1. `union_prob_le_sum`（核心）：有限计数概率空间下
     `P(⋃_{i∈s} A_i) ≤ Σ_{i∈s} P(A_i)`
     ——「并集计数 ≤ 计数和」（`Finset.card_biUnion_le`）除以样本总数；
  2. `union_bound_finite`：每个事件概率 ≤ ε ⟹ 并集概率 ≤ `|s| · ε`
     （Bonferroni 校正：k 个约束的总错误预算 = k·ε）；
  3. `multi_constraint_verification`（核心/应用）：同时验证 k 个约束、
     每个违反概率 ≤ ε ⟹ 至少一个违反的概率 ≤ kε ⟹ **全部通过的概率 ≥ 1 − kε**
     （取补集；衔接 `RealSamplingBoost` 的单约束界）；
  4. `union_bound_meas`（测度版）：`μ (⋃ i, A i) ≤ ∑' i, μ (A i)`
     （mathlib `MeasureTheory.measure_iUnion_le`，可数指标；有限指标版
     `union_bound_meas_fintype` 用 `measure_iUnion_fintype_le`）；
  5. `bonferroni_budget`（重排）：要在 k 个约束上达到总错误 ≤ δ，
     每个约束的预算需 ≤ δ/k；`bonferroni_per_event` 给出对应的概率陈述。

**诚实假设**：
  · 有限计数版：样本空间 `α` 有限（`Fintype α`）、事件为 `Finset α`、
    均匀概率 `uniformProb`（沿用 `RealSamplingBoost`）；
  · 「全部通过 ≥ 1 − kε」需要 `|α| > 0`（均匀概率分母非零）——
    否则 `1 − kε ≤ 0` 会与空样本空间下真实概率 0 冲突；
  · 测度版：`μ` 为任意测度（OuterMeasure，无需概率归一），可数指标。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open MeasureTheory

/-! ## 核心：有限计数概率空间的并集界 -/

/-- **并集界（Boole 不等式）**：`P(⋃_{i∈s} A_i) ≤ Σ_{i∈s} P(A_i)`。
证明路线：并集基数 ≤ 基数之和（`Finset.card_biUnion_le`）⟹ 同除以样本总数
（`div_le_div_of_nonneg_right`）⟹ 和的分母提取（`Finset.sum_div`）。 -/
theorem union_prob_le_sum {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (A : ι → Finset α) :
    uniformProb (s.biUnion A) ≤ ∑ i in s, uniformProb (A i) := by
  have hcard : (s.biUnion A).card ≤ ∑ i in s, (A i).card := Finset.card_biUnion_le
  have hcardR : ((s.biUnion A).card : ℝ) ≤ ∑ i in s, ((A i).card : ℝ) := by
    exact_mod_cast hcard
  unfold uniformProb
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hcardR (Nat.cast_nonneg _)

/-! ## 两个事件的并集界（`card_union_le` 版本，独立的小引理） -/

theorem union_prob_le_sum_two {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    uniformProb (A ∪ B) ≤ uniformProb A + uniformProb B := by
  have hcard : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have hcardR : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hcard
  unfold uniformProb
  rw [← add_div]
  exact div_le_div_of_nonneg_right hcardR (Nat.cast_nonneg _)

/-! ## Bonferroni 校正：k 个事件的并集界 -/

/-- 每个事件概率 ≤ ε ⟹ 并集概率 ≤ `|s| · ε`（Bonferroni 校正：
k 个事件的错误预算相加，`Σ_{i∈s} ε = |s|·ε`）。 -/
theorem union_bound_finite {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (A : ι → Finset α) {ε : ℝ}
    (hA : ∀ i ∈ s, uniformProb (A i) ≤ ε) :
    uniformProb (s.biUnion A) ≤ (s.card : ℝ) * ε := by
  calc
    uniformProb (s.biUnion A) ≤ ∑ i in s, uniformProb (A i) := union_prob_le_sum s A
    _ ≤ ∑ _i in s, ε := Finset.sum_le_sum hA
    _ = (s.card : ℝ) * ε := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 核心应用：多重约束验证 -/

/-- **多重约束验证**：同时验证 `s` 中的 k 个约束，每个约束的违反概率 ≤ ε，
则「至少一个约束被违反」的概率 ≤ `|s|·ε`，于是**全部通过的概率 ≥ 1 − |s|·ε**。
（`Finset.univ \ ⋃ A_i` 是「全部通过」事件；取补集把并集界翻转为通过率下界。） -/
theorem multi_constraint_verification {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (A : ι → Finset α) {ε : ℝ} (hN : 0 < Fintype.card α)
    (hA : ∀ i ∈ s, uniformProb (A i) ≤ ε) :
    1 - (s.card : ℝ) * ε ≤ uniformProb ((Finset.univ : Finset α) \ s.biUnion A) := by
  have hsub : s.biUnion A ⊆ (Finset.univ : Finset α) := Finset.subset_univ _
  have hcompl : uniformProb ((Finset.univ : Finset α) \ s.biUnion A)
      = 1 - uniformProb (s.biUnion A) := by
    have hle : (s.biUnion A).card ≤ (Finset.univ : Finset α).card := Finset.card_le_card hsub
    have hle' : (s.biUnion A).card ≤ Fintype.card α := by
      simpa [Finset.card_univ] using hle
    unfold uniformProb
    rw [Finset.card_sdiff hsub, Finset.card_univ, Nat.cast_sub hle', sub_div,
      div_self (ne_of_gt (Nat.cast_pos.mpr hN))]
  rw [hcompl]
  exact sub_le_sub_left (union_bound_finite s A hA) 1

/-! ## 测度版并集界 -/

/-- **测度版并集界**：`μ (⋃ i, A i) ≤ ∑' i, μ (A i)`（可数指标；
直接引用 mathlib `MeasureTheory.measure_iUnion_le`，任意测度、无需概率归一）。 -/
theorem union_bound_meas {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    (A : ι → Set α) :
    μ (⋃ i, A i) ≤ ∑' i, μ (A i) :=
  MeasureTheory.measure_iUnion_le A

/-- 有限指标的测度版并集界：`μ (⋃ i, A i) ≤ ∑ i, μ (A i)`
（`MeasureTheory.measure_iUnion_fintype_le`）。 -/
theorem union_bound_meas_fintype {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]
    (A : ι → Set α) :
    μ (⋃ i, A i) ≤ ∑ i, μ (A i) :=
  MeasureTheory.measure_iUnion_fintype_le μ A

/-! ## 错误预算分配（Bonferroni 重排） -/

/-- **预算重排**：若每个事件的概率预算 `ε ≤ δ/k`（`k > 0`），
则 k 个事件的总预算 `k·ε ≤ δ`——想在 k 个约束上达到总错误 ≤ δ，
每个约束必须做到 ≤ δ/k。 -/
theorem bonferroni_budget {k : ℕ} (hk : 0 < k) {δ ε : ℝ} (h : ε ≤ δ / (k : ℝ)) :
    (k : ℝ) * ε ≤ δ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  calc
    (k : ℝ) * ε ≤ (k : ℝ) * (δ / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)
    _ = δ := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ δ hk'

/-- **Bonferroni 分配**：每个约束的违反概率 ≤ δ/|s| ⟹ 并集（至少一个违反）
的概率 ≤ δ——把总错误预算 δ 均匀分摊到 k 个约束。 -/
theorem bonferroni_per_event {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (A : ι → Finset α) {δ : ℝ} (hk : 0 < s.card)
    (hA : ∀ i ∈ s, uniformProb (A i) ≤ δ / (s.card : ℝ)) :
    uniformProb (s.biUnion A) ≤ δ := by
  have hk' : (s.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  calc
    uniformProb (s.biUnion A) ≤ (s.card : ℝ) * (δ / (s.card : ℝ)) :=
      union_bound_finite s A hA
    _ = δ := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ δ hk'

/-! ## 注：与 RealSamplingBoost / RealRandomVerify 的衔接

  `verify_probability_guarantee`（RealRandomVerify）给单约束违背概率 ≤ ε；
  `boost_confidence`（RealSamplingBoost）把单轮 ε 放大为 k 轮 1 − ε^k。
  本文件的 `multi_constraint_verification` 补齐「多个约束**同时**验证」一环：
  同时验证 k 个约束、每个违反概率 ≤ ε ⟹ 全部通过 ≥ 1 − kε，
  用 `bonferroni_per_event` 可把总预算 δ 分摊为每约束 δ/k。
  三者组合即「多轮 × 多约束」的随机化验证完整链。
-/

end Lattice
