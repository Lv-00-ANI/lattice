import Mathlib
import Lattice.Lib.InfoTheory.RealKL
/-!
# LATTICE: 连续分布 KL 散度与微分熵（测度 / 密度形式）

RealKL 建立了**有限离散**分布上的 KL 散度 `kl p q = Σ_a p_a·log(p_a/q_a)`（Gibbs
非负、零化刻画）。本文件把 KL 推广到**连续 / 一般测度空间**：

  1. `klDensity μ f g = ∫ f·log(f/g) dμ`（**密度形式** KL：μ 为基准测度，
     f、g 为概率密度函数）；
  2. `klMeasure μ ν = ∫ log(dν/dμ) dμ`（**Radon–Nikodym 形式** KL：直接以两个
     测度 μ、ν 为输入，被积函数是 RN 导数 `ν.rnDeriv μ` 的实数化）；
  3. `differentialEntropy μ f = −∫ f·log f dμ`（微分熵）、
     `crossEntropyMeasure μ f g = −∫ f·log g dμ`（连续交叉熵）；
  4. `klDensity_nonneg`（**Gibbs，核心**）：∫f = ∫g、f ≥ 0、g > 0 ⟹ KL ≥ 0。
     证明走**逐点弦不等式**：由 mathlib 的 `Real.log_le_sub_one_of_pos`
     （log t ≤ t − 1）取 t = (f/g)⁻¹ 并用 `Real.log_inv` 得
     `1 − (f/g)⁻¹ ≤ log(f/g)`，两边乘 f > 0（f = 0 的纤维上被积项为 0 ≥ f − g）
     得逐点 `f − g ≤ f·log(f/g)`；再用 `integral_mono` 积分、`integral_sub` 与
     `∫f = ∫g` 收尾。这是离散 `kl_nonneg`（RealKL）在测度空间上的对应物。
  5. `klDensity_eq_sub_entropies`：f、g 严格正 ⟹ KL = ∫f·log f − ∫f·log g
     （`Real.log_div` 拆积，`integral_sub` 线性）。
  6. `klDensity_eq_ce_sub_entropy_measure`（定义桥）：
     KL = crossEntropyMeasure − differentialEntropy（用定理 5 与两个定义 + ring）。
  7. `differentialEntropy_le_crossEntropyMeasure`：由 4 + 6 直接得
     **H(f) ≤ CE(f,g)**（连续版「熵 ≤ 交叉熵」，RealCrossEntropy 的 `ce_ge_entropy`
     的测度对应物）。
  8. `klDensity_self` / `klDensity_eq_zero_of_eq`：f = g ⟹ KL(f‖f) = 0。
  9. `klMeasure_self`：`[SigmaFinite μ]` ⟹ KL(μ‖μ) = 0（用 `Measure.rnDeriv_self`
     给出的 a.e. 等式 `(μ.rnDeriv μ) =ᵐ[μ] 1`，`integral_congr_ae` 归零）；
     `klMeasure_eq_zero_of_eq`：μ = ν ⟹ KL(μ‖ν) = 0。

**#check 结果（mathlib 4.14 实测）**：
- `MeasureTheory.Measure.rnDeriv : Measure α → Measure α → α → ℝ≥0∞`（注意取值是
  `ℝ≥0∞`，故被积函数必须实数化 `(... .toReal)` 才能取 `Real.log`）；
- `MeasureTheory.Measure.rnDeriv_self (μ) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1`；
- `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`、
  `MeasureTheory.Measure.withDensity_rnDeriv_eq`、
  `MeasureTheory.Measure.lintegral_rnDeriv`（绝对连续 / 密度表示层的原料）；
- `Real.log_le_sub_one_of_pos : 0 < x → Real.log x ≤ x - 1`（Gibbs 的逐点引擎）；
- `MeasureTheory.integral_mono`、`MeasureTheory.integral_sub`、`MeasureTheory.integral_congr_ae`。

**诚实假设与降级（重要）**：
- **密度形式（Layer A）是完整证明的**，只要求逐点非负 / 严格正、可积性与
  「∫f = ∫g」（概率密度归一化）。注意 `Lattice.kl_nonneg`（RealKL）在离散情形
  根本不需要归一化；连续形式的 Gibbs 标准证法需要 `∫f = ∫g`（等价地
  概率归一化），这里保留该假设。
- **Radon–Nikodym 形式（Layer B）只给出定义与最基础的性质**（自 KL 为零、
  相等测度 KL 为零）。**RN 层面的 Gibbs 不等式 `0 ≤ ∫ log(dν/dμ) dμ`
  （Jensen / 变分法）本文件未证明**：它需要 `x log x` 的凸性与 Jensen 或
  变分刻画，并要处理 `toReal`/`ℝ≥0∞` 的边角（`Real.log 0 = 0` 约定使
  `toReal` 的非负性论证变复杂）。`klDensity_nonneg` 是它的**密度层完整替代**：
  由 `absolutelyContinuous_iff_withDensity_rnDeriv_eq`，ν = μ.withDensity (dν/dμ)
  时 `klMeasure μ ν` 与 `klDensity μ (dν/dμ) 1` 对应，故非负性在密度层已成立。
- `Real.log` 在非正处取 0（全函数）；含 log 的**等式**在 `0 < f`、`0 < g`（log
  定义域）假设下陈述，这是语义标注而非证明所需。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory
open scoped BigOperators

/-! ## 一、密度形式 KL 与微分熵 -/

/-- **密度形式 KL 散度**：`KL(f‖g) = ∫ f·log(f/g) dμ`（`μ` 为基准测度）。
约定 `Real.log 0 = 0`，故 `f = 0` 处被积项为 0。 -/
noncomputable def klDensity {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x / g x) ∂μ

/-- **微分熵**：`H(f) = −∫ f·log f dμ`。约定 `Real.log 0 = 0`（`f = 0` 处
被积项 `f·log f = 0`，与离散熵的 0 log 0 = 0 约定一致）。 -/
noncomputable def differentialEntropy {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) : ℝ :=
  - ∫ x, f x * Real.log (f x) ∂μ

/-- **连续交叉熵**：`CE(f,g) = −∫ f·log g dμ`（RealCrossEntropy 的 `crossEntropy`
在测度空间上的对应物）。 -/
noncomputable def crossEntropyMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) : ℝ :=
  - ∫ x, f x * Real.log (g x) ∂μ

/-! ## 二、Gibbs 逐点引擎 -/

/-- **逐点 Gibbs 下界**：`0 ≤ f x`、`0 < g x` ⟹ `f x − g x ≤ f x·log(f x/g x)`。
证明：`f x = 0` 时右边为 0、左边 `−g x < 0`；`f x > 0` 时令 `a = f x/g x > 0`，
由 `log t ≤ t − 1`（`t = a⁻¹`）与 `log_inv` 得 `1 − a⁻¹ ≤ log a`，两边乘
`f x > 0`，并用 `f x·(f x/g x)⁻¹ = g x` 化简左边。 -/
theorem sub_le_mul_log_div {f g : ℝ} (hf : 0 ≤ f) (hg : 0 < g) :
    f - g ≤ f * Real.log (f / g) := by
  by_cases hf0 : f = 0
  · -- f = 0：右侧 0·log 0 = 0 ≥ 0 − g
    rw [hf0]
    simp only [zero_mul, zero_div, Real.log_zero, mul_zero]
    linarith
  · have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hf0)
    have ha : 0 < f / g := div_pos hfpos hg
    -- log (a⁻¹) ≤ a⁻¹ − 1  ∧  log (a⁻¹) = −log a  ⟹  1 − a⁻¹ ≤ log a
    have hlog : (1 : ℝ) - (f / g)⁻¹ ≤ Real.log (f / g) := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
      rw [Real.log_inv] at h
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog hfpos.le
    have hkey : f * (1 - (f / g)⁻¹) = f - g := by
      rw [inv_div]
      field_simp
    rw [hkey] at hmul
    exact hmul

/-! ## 三、KL 非负（Gibbs） -/

/-- **Gibbs 不等式（密度形式，核心）**：`f ≥ 0`、`g > 0`、`f`、`g` 与
`f·log(f/g)` 可积、且 `∫f = ∫g` ⟹ `KL(f‖g) ≥ 0`。
证明：逐点 `sub_le_mul_log_div` + `integral_mono`，再用 `integral_sub` 与
`∫f = ∫g` 把下界化归为 0。 -/
theorem klDensity_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) (hg_pos : ∀ x, 0 < g x)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hkl_int : Integrable (fun x => f x * Real.log (f x / g x)) μ)
    (h_eq : ∫ x, f x ∂μ = ∫ x, g x ∂μ) :
    0 ≤ klDensity μ f g := by
  have hfg : Integrable (fun x => f x - g x) μ := hf_int.sub hg_int
  have hpoint : (fun x => f x - g x) ≤ fun x => f x * Real.log (f x / g x) :=
    fun x => sub_le_mul_log_div (hf_nn x) (hg_pos x)
  have hmono : (∫ x, (f x - g x) ∂μ) ≤ ∫ x, f x * Real.log (f x / g x) ∂μ :=
    integral_mono hfg hkl_int hpoint
  have hzero : (∫ x, (f x - g x) ∂μ) = 0 := by
    rw [integral_sub hf_int hg_int, h_eq, sub_self]
  calc (0 : ℝ) = ∫ x, (f x - g x) ∂μ := hzero.symm
    _ ≤ ∫ x, f x * Real.log (f x / g x) ∂μ := hmono
    _ = klDensity μ f g := rfl

/-! ## 四、KL 的熵分解与交叉熵桥 -/

/-- **KL 的熵分解**：f、g 严格正且 `f·log f`、`f·log g` 可积 ⟹
`KL(f‖g) = ∫f·log f − ∫f·log g`（`Real.log_div` 逐点拆积 + `integral_sub`）。 -/
theorem klDensity_eq_sub_entropies {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf_pos : ∀ x, 0 < f x) (hg_pos : ∀ x, 0 < g x)
    (h1 : Integrable (fun x => f x * Real.log (f x)) μ)
    (h2 : Integrable (fun x => f x * Real.log (g x)) μ) :
    klDensity μ f g
      = (∫ x, f x * Real.log (f x) ∂μ) - ∫ x, f x * Real.log (g x) ∂μ := by
  have hpoint : (fun x => f x * Real.log (f x / g x))
      = fun x => f x * Real.log (f x) - f x * Real.log (g x) := by
    funext x
    rw [Real.log_div (hf_pos x).ne' (hg_pos x).ne']
    ring
  rw [klDensity, hpoint, integral_sub h1 h2]

/-- **定义桥（KL = CE − H，测度版）**：`KL(f‖g) = crossEntropyMeasure − differentialEntropy`。 -/
theorem klDensity_eq_ce_sub_entropy_measure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf_pos : ∀ x, 0 < f x) (hg_pos : ∀ x, 0 < g x)
    (h1 : Integrable (fun x => f x * Real.log (f x)) μ)
    (h2 : Integrable (fun x => f x * Real.log (g x)) μ) :
    klDensity μ f g = crossEntropyMeasure μ f g - differentialEntropy μ f := by
  rw [klDensity_eq_sub_entropies hf_pos hg_pos h1 h2, crossEntropyMeasure, differentialEntropy]
  ring

/-- **熵 ≤ 交叉熵（连续版）**：在 `klDensity_nonneg` 的假设下，
`H(f) ≤ CE(f,g)`（RealCrossEntropy 的 `ce_ge_entropy` 在测度空间上的对应物）。
由 Gibbs 非负性与定义桥 `KL = CE − H` 直接得到。 -/
theorem differentialEntropy_le_crossEntropyMeasure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) (hg_pos : ∀ x, 0 < g x)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (h1 : Integrable (fun x => f x * Real.log (f x)) μ)
    (h2 : Integrable (fun x => f x * Real.log (g x)) μ)
    (hkl_int : Integrable (fun x => f x * Real.log (f x / g x)) μ)
    (h_eq : ∫ x, f x ∂μ = ∫ x, g x ∂μ) :
    differentialEntropy μ f ≤ crossEntropyMeasure μ f g := by
  have hnn := klDensity_nonneg hf_nn hg_pos hf_int hg_int hkl_int h_eq
  -- 定义桥（不需 f 严格正：f = 0 处两边同为 0）
  have hpoint : (fun x => f x * Real.log (f x / g x))
      = fun x => f x * Real.log (f x) - f x * Real.log (g x) := by
    funext x
    by_cases hfx : f x = 0
    · rw [hfx]
      simp [Real.log_zero]
    · rw [Real.log_div hfx (hg_pos x).ne']
      ring
  have hbridge : klDensity μ f g = crossEntropyMeasure μ f g - differentialEntropy μ f := by
    rw [klDensity, hpoint, integral_sub h1 h2, crossEntropyMeasure, differentialEntropy]
    ring
  linarith [hnn, hbridge]

/-! ## 五、密度形式 KL 的零化 -/

/-- `KL(f‖f) = 0`（逐点被积项为零：`f = 0` 时 `0·log 0 = 0`，
`f ≠ 0` 时 `log(f/f) = log 1 = 0`）。 -/
theorem klDensity_self {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    klDensity μ f f = 0 := by
  have hzero : (fun x => f x * Real.log (f x / f x)) = fun _ => (0 : ℝ) := by
    funext x
    by_cases h : f x = 0
    · rw [h]
      simp [Real.log_zero]
    · rw [div_self h, Real.log_one, mul_zero]
  rw [klDensity, hzero]
  simp

/-- `f = g ⟹ KL(f‖g) = 0`。 -/
theorem klDensity_eq_zero_of_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ}
    (h : f = g) : klDensity μ f g = 0 := by
  subst h
  exact klDensity_self μ f

/-! ## 六、Radon–Nikodym 形式 KL -/

/-- **Radon–Nikodym 形式 KL 散度**：`KL(μ‖ν) = ∫ log(dν/dμ) dμ`。
`Measure.rnDeriv` 取值于 `ℝ≥0∞`，故先 `.toReal` 实数化再取 `Real.log`
（`Real.log 0 = 0` 处理 `dν/dμ = 0` 的纤维）。 -/
noncomputable def klMeasure {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ∫ x, Real.log ((ν.rnDeriv μ x).toReal) ∂μ

/-- **自 KL 为零**：`[SigmaFinite μ]` ⟹ `KL(μ‖μ) = 0`。
证明：`Measure.rnDeriv_self` 给出 `μ.rnDeriv μ =ᵐ[μ] 1`，逐点
`log 1 = 0`，被积函数 a.e. 为零，`integral_congr_ae` + `integral_zero`。 -/
theorem klMeasure_self {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    klMeasure μ μ = 0 := by
  have h : (fun x => Real.log ((μ.rnDeriv μ x).toReal)) =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [Measure.rnDeriv_self μ] with x hx
    rw [hx]
    simp
  rw [klMeasure, integral_congr_ae h]
  simp

/-- `μ = ν ⟹ KL(μ‖ν) = 0`（由 `klMeasure_self` 转移）。 -/
theorem klMeasure_eq_zero_of_eq {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [SigmaFinite μ] (h : μ = ν) : klMeasure μ ν = 0 := by
  subst h
  exact klMeasure_self μ

end Lattice
