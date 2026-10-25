import Mathlib

/-!
# LATTICE: 离散有限可选停止（Optional Stopping）

`RealAzumaMartingale` 用**有限纤维条件期望**做鞅差；其 docstring 明确标注多期滤链
与停时结构未做。本文件在 mathlib 的离散鞅框架（`Filtration ℕ m0` + `Martingale`）
上建立**有限时间 / 有界停时**的可选停止定理：

  1. `stoppedValue_neg`：停时值的取负交换 `stoppedValue (−f) τ = −stoppedValue f τ`。
  2. `martingale_expected_stoppedValue_eq`（**核心**）：鞅 `M` + 有界停时 `τ ≤ N`
     ⟹ `E[M_τ] = E[M_0]`。
     证明路线：mathlib 的 `Submartingale.expected_stoppedValue_mono` 给出
     `E[M_τ] ≤ E[M_0]`（用 `Martingale.submartingale`）与 `E[M_0] ≤ E[M_τ]`
     （用 `Martingale.neg` 对 `−M` 施加），两边夹。
  3. `martingale_expected_stoppedValue_eq_of_le`：`τ ≤ π` 两个有界停时
     ⟹ `E[M_τ] = E[M_π]`。
  4. `martingale_expected_stoppedValue_eq_last`：`τ ≤ N` ⟹ `E[M_τ] = E[M_N]`。
  5. `martingale_expected_stoppedValue_min_eq`：**`τ ≤ n` 有界化版本**
     `E[M_{min τ n}] = E[M_0]`（`IsStoppingTime.min`）。
  6. `martingale_stoppedValue_bound`：若 `|M_k| ≤ C`（`k ≤ N`），则
     `|E[M_τ]| ≤ C`（逐点界 + `abs_integral_le_integral_abs`）。

**诚实边界（标注）**：
- 这是 mathlib 的**一般测度论**离散鞅版本（不是有限状态/有限计数版），
  前提使用 `[SigmaFiniteFiltration μ 𝒢]`。
- 未做：连续时间可选停止；无界停时的收敛型结果（需要一致可积/控制收敛）；
  与 `RealStochasticProcess` 有限纤维鞅差定义的桥接。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}

/-! ## 一、停时值的取负交换 -/

/-- 停时值对函数取负交换：`stoppedValue (−f) τ = −stoppedValue f τ`。 -/
theorem stoppedValue_neg (f : ℕ → Ω → ℝ) (τ : Ω → ℕ) :
    stoppedValue (-f) τ = -stoppedValue f τ := by
  funext ω
  rfl

/-! ## 二、核心：有界停时的 `E[M_τ] = E[M_0]` -/

/-- **可选停止（有限时间版，核心）**：鞅 `f` + 停时 `τ` 有界（`τ ≤ N`）
⟹ `E[f_τ] = E[f_0]`。
证明：对 `f`（下鞅）与 `−f`（下鞅）分别用
`Submartingale.expected_stoppedValue_mono`，得到双向不等式后两边夹。 -/
theorem martingale_expected_stoppedValue_eq (f : ℕ → Ω → ℝ) (hf : Martingale f 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] {τ : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ}
    (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  have hge : ∫ ω, f 0 ω ∂μ ≤ ∫ ω, stoppedValue f τ ω ∂μ := by
    have h := MeasureTheory.Submartingale.expected_stoppedValue_mono (N := N)
      hf.submartingale (isStoppingTime_const 𝒢 0) hτ (fun ω => Nat.zero_le _) hbdd
    simpa [MeasureTheory.stoppedValue_const] using h
  have hle : ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, f 0 ω ∂μ := by
    have h := MeasureTheory.Submartingale.expected_stoppedValue_mono (N := N)
      hf.neg.submartingale (isStoppingTime_const 𝒢 0) hτ (fun ω => Nat.zero_le _) hbdd
    simp only [MeasureTheory.stoppedValue_const] at h
    rw [show stoppedValue (-f) τ = -stoppedValue f τ from stoppedValue_neg f τ] at h
    simp only [Pi.neg_apply, integral_neg] at h
    linarith
  exact le_antisymm hle hge

/-- **可选停止（两个有界停时）**：`τ ≤ π`、`π` 有界 ⟹ `E[f_τ] = E[f_π]`。 -/
theorem martingale_expected_stoppedValue_eq_of_le (f : ℕ → Ω → ℝ) (hf : Martingale f 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] {τ π : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ)
    (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, stoppedValue f π ω ∂μ := by
  have h1 : ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ :=
    MeasureTheory.Submartingale.expected_stoppedValue_mono (N := N)
      hf.submartingale hτ hπ hle hbdd
  have h2 : ∫ ω, stoppedValue f π ω ∂μ ≤ ∫ ω, stoppedValue f τ ω ∂μ := by
    have h := MeasureTheory.Submartingale.expected_stoppedValue_mono (N := N)
      hf.neg.submartingale hτ hπ hle hbdd
    rw [show stoppedValue (-f) τ = -stoppedValue f τ from stoppedValue_neg f τ,
      show stoppedValue (-f) π = -stoppedValue f π from stoppedValue_neg f π] at h
    simp only [Pi.neg_apply, integral_neg] at h
    linarith
  exact le_antisymm h1 h2

/-- **`E[M_τ] = E[M_N]`**：`τ ≤ N` 有界停时的末时刻形式。 -/
theorem martingale_expected_stoppedValue_eq_last (f : ℕ → Ω → ℝ) (hf : Martingale f 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] {τ : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ}
    (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f N ω ∂μ := by
  have h := martingale_expected_stoppedValue_eq_of_le f hf hτ (isStoppingTime_const 𝒢 N)
    (fun ω => hbdd ω) (N := N) (fun _ => le_refl N)
  simpa [MeasureTheory.stoppedValue_const] using h

/-- **`τ ≤ n` 有界化版本**：`E[M_{min τ n}] = E[M_0]`（`IsStoppingTime.min`）。 -/
theorem martingale_expected_stoppedValue_min_eq (f : ℕ → Ω → ℝ) (hf : Martingale f 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] {τ : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ) (n : ℕ) :
    ∫ ω, stoppedValue f (fun ω => min (τ ω) n) ω ∂μ = ∫ ω, f 0 ω ∂μ :=
  martingale_expected_stoppedValue_eq f hf (hτ.min (isStoppingTime_const 𝒢 n))
    (fun _ => min_le_right _ _)

/-! ## 三、有界鞅的停时期望界 -/

/-- **停时期望的界**：若 `|f k ω| ≤ C`（对 `k ≤ N`，`τ ≤ N`），则
`|E[f_τ]| ≤ C`（逐点界 + 经 `Real.norm_eq_abs` 转换后的
`norm_integral_le_integral_norm` + 常数积分）。
本定理需 `[IsProbabilityMeasure μ]`：它是 `∫ _ω, C ∂μ = C` 成立的前提，
因而概率测度假设不可省。 -/
theorem martingale_stoppedValue_bound (f : ℕ → Ω → ℝ) [IsProbabilityMeasure μ]
    {τ : Ω → ℕ} {N : ℕ} {C : ℝ} (hbdd : ∀ ω, τ ω ≤ N)
    (hC : ∀ k, k ≤ N → ∀ ω, |f k ω| ≤ C) :
    |∫ ω, stoppedValue f τ ω ∂μ| ≤ C := by
  have hpoint : ∀ ω, |stoppedValue f τ ω| ≤ C := fun ω => hC (τ ω) (hbdd ω) ω
  have habs : |∫ ω, stoppedValue f τ ω ∂μ| ≤ ∫ ω, |stoppedValue f τ ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun ω => stoppedValue f τ ω) (μ := μ)
  have hmono : (∫ ω, |stoppedValue f τ ω| ∂μ) ≤ ∫ _ω : Ω, C ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
      (integrable_const C) (Filter.Eventually.of_forall hpoint)
  have hconst : (∫ _ω : Ω, C ∂μ) = C := by
    rw [MeasureTheory.integral_const, MeasureTheory.measure_univ]
    norm_num
  linarith [habs, hmono, hconst]

end Lattice
