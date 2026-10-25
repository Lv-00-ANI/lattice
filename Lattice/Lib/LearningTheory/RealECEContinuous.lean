import Mathlib
import Lattice.Lib.LearningTheory.RealCalibration
/-!
# LATTICE: 连续分布 ECE（Expected Calibration Error）与 Brier 桥

`RealCalibration` 给出的是**离散分箱**版 ECE（`ece w acc conf = Σ_b w_b·|acc_b − conf_b|`）
与 `ece_le_sqrt_brier`（分箱 Cauchy–Schwarz）。本文件将其提升为**测度论连续版**：

  1. `eceContinuous`（定义）：`ECE = ∫ x, |acc x − conf x| ∂μ`。
  2. `brierContinuous`（定义）：`Brier = ∫ x, (acc x − conf x)² ∂μ`。
  3. `eceContinuous_nonneg`：`0 ≤ ECE`（`integral_nonneg`）。
  4. `eceContinuous_self` / `eceContinuous_eq_zero_iff`：**校准完美 ⟺ ECE = 0**，
     在「几乎处处相等」意义下成立
     （`integral_eq_zero_iff_of_nonneg_ae` + `abs_eq_zero`）。
  5. `eceContinuous_le_sqrt_brier`（**核心**）：`ECE ≤ √Brier`，用积分型 Hölder
     （`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`，`p = q = 2`）+
     `Real.sqrt_eq_rpow`。

**诚实边界（标注）**：
- 定理 5 需要 `ACStronglyMeasurable`/可积性显式假设（不证可测性）；
  `[IsProbabilityMeasure μ]` 用于把 `∫ 1` 归一为 1。
- 未做：与 `RealCalibration.ece`（有限分箱版）的**逐点桥接**（需要在有限类型上
  构造均匀计数测度并证明分箱求和 = 积分），以及「校准完美」的分布级刻画。
- 未做：`overconfContinuous` 的连续版（离散版见 `RealCalibration.overconf_le_ece`）。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open MeasureTheory
open scoped BigOperators

/-! ## 一、定义 -/

/-- **连续 ECE**：`ECE = ∫ |acc(conf) − conf| dμ`（`acc`、`conf` 为逐点精度与置信度）。 -/
noncomputable def eceContinuous {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (acc conf : α → ℝ) : ℝ :=
  ∫ x, |acc x - conf x| ∂μ

/-- **连续 Brier 分数**：`Brier = ∫ (acc(conf) − conf)² dμ`。 -/
noncomputable def brierContinuous {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (acc conf : α → ℝ) : ℝ :=
  ∫ x, (acc x - conf x) ^ 2 ∂μ

/-! ## 二、非负性 -/

/-- **ECE 非负**：`0 ≤ ECE`（被积函数逐点非负，`integral_nonneg`）。 -/
theorem eceContinuous_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (acc conf : α → ℝ) : 0 ≤ eceContinuous μ acc conf :=
  integral_nonneg fun _ => abs_nonneg _

/-- **完美校准 ⟹ ECE = 0**：`acc = conf` 逐点，则 `ECE = 0`。 -/
theorem eceContinuous_self {α : Type*} [MeasurableSpace α] (μ : Measure α) (acc : α → ℝ) :
    eceContinuous μ acc acc = 0 := by
  unfold eceContinuous
  have : (fun x => |acc x - acc x|) = fun _ => (0 : ℝ) := by
    funext x
    rw [sub_self, abs_zero]
  rw [this, integral_zero]

/-! ## 三、ECE = 0 ⟺ 几乎处处校准完美 -/

/-- **ECE = 0 ⟺ 几乎处处校准完美**：在 `|acc − conf|` 可积的前提下，
`ECE = 0` 当且仅当 `acc =ᵐ[μ] conf`。
证明：`integral_eq_zero_iff_of_nonneg_ae` 把 `∫ |u| = 0` 化为 `|u| =ᵐ[μ] 0`，
再用 `abs_eq_zero`。 -/
theorem eceContinuous_eq_zero_iff {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {acc conf : α → ℝ} (hint : Integrable (fun x => |acc x - conf x|) μ) :
    eceContinuous μ acc conf = 0 ↔ acc =ᵐ[μ] conf := by
  unfold eceContinuous
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hint]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)
  · intro h
    filter_upwards [h] with x hx
    show |acc x - conf x| = 0
    rw [hx, sub_self, abs_zero]

/-! ## 四、ECE ≤ √Brier（积分型 Cauchy–Schwarz） -/

/-- **核心：ECE ≤ √Brier**（积分型 Cauchy–Schwarz / `p = q = 2` 的 Hölder）。
证明：`∫ |u|·1 ≤ (∫ |u|²)^{1/2}·(∫ 1²)^{1/2} = (∫ u²)^{1/2} = √Brier`。 -/
theorem eceContinuous_le_sqrt_brier {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {acc conf : α → ℝ}
    (hmeas : AEStronglyMeasurable (fun x => acc x - conf x) μ)
    (hint : Integrable (fun x => (acc x - conf x) ^ 2) μ) :
    eceContinuous μ acc conf ≤ Real.sqrt (brierContinuous μ acc conf) := by
  have hpq : (2 : ℝ).IsConjExponent 2 := by
    rw [Real.isConjExponent_iff_eq_conjExponent (show (1 : ℝ) < 2 by norm_num)]
    norm_num [Real.conjExponent]
  have hmeas_abs : AEStronglyMeasurable (fun x => |acc x - conf x|) μ := hmeas.norm
  have hmem1 : Memℒp (fun x => |acc x - conf x|) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact (MeasureTheory.memℒp_two_iff_integrable_sq hmeas_abs).2
      (hint.congr (Filter.Eventually.of_forall fun x => (sq_abs (acc x - conf x)).symm))
  have hmem2 : Memℒp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact (MeasureTheory.memℒp_two_iff_integrable_sq aestronglyMeasurable_const).2
      (by simp)
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun x => |acc x - conf x|) (g := fun _ : α => (1 : ℝ))
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => by norm_num)
    hmem1 hmem2
  have hL : (∫ x, (fun x => |acc x - conf x|) x ^ (2 : ℝ) ∂μ)
      = ∫ x, (acc x - conf x) ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [Real.rpow_two, sq_abs]
  have hR : (∫ x, (fun _ : α => (1 : ℝ)) x ^ (2 : ℝ) ∂μ) = 1 := by
    have hone : (fun x : α => (fun _ : α => (1 : ℝ)) x ^ (2 : ℝ)) = fun _ => (1 : ℝ) := by
      funext x
      rw [Real.one_rpow]
    rw [hone, MeasureTheory.integral_const, MeasureTheory.measure_univ]
    norm_num
  simp only [Pi.mul_apply] at hholder
  rw [hL, hR] at hholder
  simpa [eceContinuous, brierContinuous, Real.sqrt_eq_rpow, one_mul] using hholder

end Lattice
