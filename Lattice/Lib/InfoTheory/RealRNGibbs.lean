import Mathlib
import Lattice.Lib.InfoTheory.RealContinuousKL
/-!
# LATTICE: Radon–Nikodym 层的 Gibbs 不等式（KL ≥ 0 的 RN 形式）

`RealContinuousKL` 在 docstring 中**明确标注未证**其 RN（Radon–Nikodym）定义层
`klMeasure` 的非负性。本文件补齐该缺口，并**纠正原任务书中的符号方向**。

## 关键更正（命题为假，不证）

任务书要求证明 `0 ≤ ∫ log((ν.rnDeriv μ).toReal) dμ`。在 mathlib 的约定下
`μ.rnDeriv ν` 是 **dμ/dν**（见 `Measure.withDensity_rnDeriv_eq : ν.withDensity (μ.rnDeriv ν) = μ`），
因此 `ν.rnDeriv μ = dν/dμ =: ρ`，而概率测度下

    ∫ log ρ dμ ≤ log (∫ ρ dμ) = log (ν univ) = 0      （Jensen，log 凹）

即该积分**非正**而非非负。**该字面命题是假的**，本文件给出机器验证的数值反例
`logRatio_expectation_negative`（对应 μ = ½δ₀+½δ₁、ν = ¼δ₀+¾δ₁ 时 ρ = ½, 3/2），
并改为证明正确方向的 `rnDerivLog_integral_nonpos`（≤ 0）。

## 主要结果

  1. `rnDerivLog_integral_nonpos`（**核心，正确符号**）：概率测度 `μ, ν`、`ν ≪ μ`、
     `μ ≪ ν`（保证 `ρ > 0` a.e.）⟹ `∫ log((ν.rnDeriv μ).toReal) dμ ≤ 0`。
     证明：a.e. 逐点 `log ρ ≤ ρ − 1`（`Real.log_le_sub_one_of_pos`，`rnDeriv_pos'`
     给 a.e. 正性）+ `integral_mono_ae` + `∫ ρ dμ = ν univ = 1`
     （`Measure.integral_toReal_rnDeriv`）+ `ρ` 的 `μ`-可积性
     （`Measure.integrable_toReal_rnDeriv`，`Lebesgue.lean:361`；**已证，非假设**）。
  2. `klMeasure_nonpos`：`RealContinuousKL.klMeasure μ ν ≤ 0`（直接由 1 与定义）。
  3. `rnDeriv_gibbs`（**真正的 RN Gibbs，补 RealContinuousKL 的标注缺口**）：
     概率 `μ`、`ν ≪ μ`、`ρ = dν/dμ`，则
     `0 ≤ ∫ ρ·log ρ dμ`（= KL(ν‖μ) ≥ 0）。
     证明：逐点 `ρ − 1 ≤ ρ·log ρ`（`RealContinuousKL.sub_le_mul_log_div` 取 g = 1）
     + `integral_mono` + `∫(ρ − 1) = 1 − 1 = 0` + `ρ` 的 `μ`-可积性
     （`Measure.integrable_toReal_rnDeriv`，**已证，非假设**）。
  4. `logRatio_expectation_negative`（**机器验证反例**）：`½log(½) + ½log(3/2) < 0`。

**诚实边界（标注）**：
- 定理 1 需要 `μ ≪ ν`（互绝对连续）以保证 `ρ > 0` a.e.；仅 `ν ≪ μ` 时 `ρ` 可在
  正 `μ`-测度集上取 0，`Real.log 0 = 0` 的约定会破坏 Jensen 型推导（这也是
  `∫ log ρ ≤ 0` 在仅有 `ν ≪ μ` 时不成立的原因）。
- 定理 1 与 3 **仍保留** `hint`（分别为 `log ρ`、`ρ·log ρ` 的 `μ`-可积性）：
  mathlib 中**不存在**任意实函数的 `Integrable.log` / `Integrable.mul_log`
  （已 grep 全库确认，二者只在 `IntervalIntegrable` 一侧存在；`Real.log` 在 0 附近
  无界，故对一般可积函数**不成立**），也没有针对 `rnDeriv` 的无条件版本，
  故如实保留为显式假设。**此前把 `hintρ` 一并外置的理由不成立**——mathlib **有**
  `Measure.integrable_toReal_rnDeriv`（`Lebesgue.lean:361`），`hintρ` 已删除、改为证出。
- 反例 `logRatio_expectation_negative` 是**数值核心**的机器验证；其测度论实例
  （μ = ½δ₀+½δ₁、ν = ¼δ₀+¾δ₁，ρ = dν/dμ = ½, 3/2）在 docstring 说明，
  完整的测度构造在本文件**未形式化**（标注）。
- 未做：`∫ log ρ = 0 ⟺ ν = μ` 的严格性刻画（需严格 Jensen）。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open MeasureTheory
open scoped BigOperators

/-- **RN 层 Gibbs 的方向（正确符号）**：概率测度 `μ, ν`、`ν ≪ μ`、`μ ≪ ν`、
`log(dν/dμ)` 可积 ⟹ `∫ log((ν.rnDeriv μ).toReal) ∂μ ≤ 0`。

**注意**：任务书要求的 `0 ≤ ∫ log(dν/dμ)` 是**假命题**（正确方向为 `≤ 0`），
见 `logRatio_expectation_negative`。

**已无不可证假设**：`ρ = dν/dμ` 的 `μ`-可积性此前作为显式假设 `hintρ` 引入；现由
mathlib 的 `Measure.integrable_toReal_rnDeriv`（`MeasureTheory/Decomposition/Lebesgue.lean:361`，
语句 `Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν`，本处取 `τ := ν`、`υ := μ` 即得
`Integrable (fun x => (ν.rnDeriv μ x).toReal) μ`，**方向精确匹配**）证出，
**故本定理不再假设 `hintρ`**。

仍保留的假设：`hint`（`log ρ` 的 `μ`-可积性）——mathlib 无 `Integrable.log`（0 附近无界，
故对一般可积函数为假），如实保留。 -/
theorem rnDerivLog_integral_nonpos {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SigmaFinite μ] [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition μ]
    (hac : ν ≪ μ) (hmut : μ ≪ ν)
    (hint : Integrable (fun x => Real.log ((ν.rnDeriv μ x).toReal)) μ) :
    ∫ x, Real.log ((ν.rnDeriv μ x).toReal) ∂μ ≤ 0 := by
  have hintρ : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ :=
    Measure.integrable_toReal_rnDeriv
  have hint1 : Integrable (fun x => (ν.rnDeriv μ x).toReal - 1) μ :=
    hintρ.sub (integrable_const (1 : ℝ))
  have hρ : ∫ x, (ν.rnDeriv μ x).toReal ∂μ = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac, measure_univ]
    simp
  have hpoint : (fun x => Real.log ((ν.rnDeriv μ x).toReal))
      ≤ᵐ[μ] fun x => (ν.rnDeriv μ x).toReal - 1 := by
    filter_upwards [Measure.rnDeriv_pos' hmut, Measure.rnDeriv_ne_top ν μ] with x hx hxtop
    have hx' : (0 : ℝ) < (ν.rnDeriv μ x).toReal :=
      ENNReal.toReal_pos_iff.mpr ⟨hx, lt_top_iff_ne_top.mpr hxtop⟩
    have := Real.log_le_sub_one_of_pos hx'
    linarith
  have hzero : (∫ x, ((ν.rnDeriv μ x).toReal - 1) ∂μ) = 0 := by
    rw [integral_sub hintρ (integrable_const (1 : ℝ)), hρ]
    simp
  calc ∫ x, Real.log ((ν.rnDeriv μ x).toReal) ∂μ
      ≤ ∫ x, ((ν.rnDeriv μ x).toReal - 1) ∂μ := integral_mono_ae hint hint1 hpoint
    _ = 0 := hzero

/-- **`RealContinuousKL.klMeasure` 非正**：把定理 1 接到既有定义层
`klMeasure μ ν = ∫ log((ν.rnDeriv μ).toReal) dμ` 上。 -/
theorem klMeasure_nonpos {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SigmaFinite μ] [SigmaFinite ν]
    [ν.HaveLebesgueDecomposition μ]
    (hac : ν ≪ μ) (hmut : μ ≪ ν)
    (hint : Integrable (fun x => Real.log ((ν.rnDeriv μ x).toReal)) μ) :
    klMeasure μ ν ≤ 0 :=
  rnDerivLog_integral_nonpos hac hmut hint

/-- **Radon–Nikodym 层的 Gibbs 不等式（正确形式，补 RealContinuousKL 的标注缺口）**：
概率 `μ`、`ν ≪ μ`、`ρ = dν/dμ`，且 `ρ·log ρ` 可积 ⟹ `0 ≤ ∫ ρ·log ρ dμ`
（即离散步 KL(ν‖μ) ≥ 0 的 RN 形式）。
证明：逐点 `ρ − 1 ≤ ρ·log ρ`（`sub_le_mul_log_div` 取 `g = 1`）+ `integral_mono`
+ `∫(ρ−1) dμ = 1 − 1 = 0`。

**已无不可证假设**：同定理 1，`ρ` 的 `μ`-可积性由
`Measure.integrable_toReal_rnDeriv`（`Lebesgue.lean:361`，取 `τ := ν`、`υ := μ`）证出，
**故本定理不再假设 `hintρ`**；仅保留 `hint`（`ρ·log ρ` 的 `μ`-可积性）。 -/
theorem rnDeriv_gibbs {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SigmaFinite μ] [SigmaFinite ν]
    (hac : ν ≪ μ)
    (hint : Integrable (fun x => (ν.rnDeriv μ x).toReal
      * Real.log ((ν.rnDeriv μ x).toReal)) μ) :
    0 ≤ ∫ x, (ν.rnDeriv μ x).toReal * Real.log ((ν.rnDeriv μ x).toReal) ∂μ := by
  have hintρ : Integrable (fun x => (ν.rnDeriv μ x).toReal) μ :=
    Measure.integrable_toReal_rnDeriv
  have hint1 : Integrable (fun x => (ν.rnDeriv μ x).toReal - 1) μ :=
    hintρ.sub (integrable_const (1 : ℝ))
  have hρ : ∫ x, (ν.rnDeriv μ x).toReal ∂μ = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac, measure_univ]
    simp
  have hpoint : (fun x => (ν.rnDeriv μ x).toReal - 1)
      ≤ fun x => (ν.rnDeriv μ x).toReal * Real.log ((ν.rnDeriv μ x).toReal) := by
    intro x
    simpa [div_one] using
      sub_le_mul_log_div (ENNReal.toReal_nonneg) (by norm_num : (0 : ℝ) < 1)
  have hzero : (∫ x, ((ν.rnDeriv μ x).toReal - 1) ∂μ) = 0 := by
    rw [integral_sub hintρ (integrable_const (1 : ℝ)), hρ]
    simp
  have hmono : (∫ x, ((ν.rnDeriv μ x).toReal - 1) ∂μ)
      ≤ ∫ x, (ν.rnDeriv μ x).toReal * Real.log ((ν.rnDeriv μ x).toReal) ∂μ :=
    integral_mono hint1 hint hpoint
  linarith

/-! ## 机器验证的反例：字面命题 `0 ≤ ∫ log(dν/dμ) dμ` 为假 -/

/-- **反例（机器验证）**：`½·log(½) + ½·log(3/2) < 0`。

取 `μ = ½δ₀ + ½δ₁`（概率测度）与 `ν = ¼δ₀ + ¾δ₁`（概率测度），
则 `ρ = dν/dμ = (½, 3/2)` 且
`∫ log ρ dμ = ½·log(½) + ½·log(3/2) = ½·log(3/4) < 0`。
这直接否证了「`0 ≤ ∫ log((ν.rnDeriv μ).toReal) dμ`」这一字面命题
（该字面命题**未证**，因为它为假；本文件证明的是正确方向的
`rnDerivLog_integral_nonpos`）。 -/
theorem logRatio_expectation_negative :
    (1 / 2 : ℝ) * Real.log (1 / 2) + (1 / 2 : ℝ) * Real.log (3 / 2) < 0 := by
  have h : Real.log ((1 / 2 : ℝ) * (3 / 2)) < 0 := by
    rw [Real.log_neg_iff (by norm_num : (0 : ℝ) < 1 / 2 * (3 / 2))]
    norm_num
  have h2 := Real.log_mul (show (1 / 2 : ℝ) ≠ 0 by norm_num)
    (show (3 / 2 : ℝ) ≠ 0 by norm_num)
  nlinarith [h, h2]

/-- 反例的「乘积形式」：`½·log(3/4) < 0`（等价重述，便于机验）。 -/
theorem logRatio_half_log_three_quarters_negative :
    (1 / 2 : ℝ) * Real.log (3 / 4) < 0 := by
  have h : Real.log (3 / 4 : ℝ) < 0 := by
    rw [Real.log_neg_iff (by norm_num : (0 : ℝ) < 3 / 4)]
    norm_num
  linarith

end Lattice
