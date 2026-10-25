import Mathlib
import Lattice.Lift.RealRandomVerify
/-!
# LATTICE: 测度论 Hoeffding / Chernoff —— 独立变量之和的指数型尾界

RealHoeffding / RealAzuma 的 Hoeffding 界是**有限计数概率空间**（均匀乘积空间 +
`Finset.prod_univ_sum` 分解）的版本；RealRandomVerify.markov_bound 给出的是
测度论但**多项式型**的尾界。本文件把二者升级为**测度论 + 指数型**：

  1. `mgf_factor_measure`（**独立性 ⟹ MGF 因子分解，核心**）：对有限指标集
     `ι`，`iIndepFun`（mathlib 的独立族）+ 逐分量可测 ⟹
     `mgf (∑ i, X i) μ t = ∏ i, mgf (X i) μ t`。
     证明**直接调用 mathlib 既有** `ProbabilityTheory.iIndepFun.mgf_sum`
     （`Finset.univ` 上），再做 `∑ i ∈ univ` / `∑ i` 与 `∏` 的记法对齐。
  2. `mgf_sum_pair`：`ι = Fin 2` 的具体情形（加法化归为两个 MGF 之积）。
  3. `mgf_bound_of_coordinate_bounds`（**逐坐标界 ⟹ 和的 MGF 界**）：
     若每个分量满足 `mgf (X i) μ t ≤ exp(t²·cᵢ²/2)`，则
     `mgf (∑ X i) μ t ≤ exp(t²·(∑ cᵢ²)/2)`。
     证明：定理 1 因子分解 + `Finset.prod_le_prod`（配 `mgf_nonneg`）+
     `Real.exp_sum` 合并指数 + `Finset.mul_sum` / `Finset.sum_div` 提出常数。
  4. `hoeffding_tail_of_mgf_bound`（**测度版 Chernoff 桥，核心**）：
     `[IsFiniteMeasure μ]`、`σ² > 0`、`ε > 0`，给定
     `mgf S μ (ε/σ²) ≤ exp((ε/σ²)²·σ²/2)` 与相应可积性，则
     `(μ {ε ≤ S}).toReal ≤ exp(−ε²/(2σ²))`。
     证明：mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf`（Chernoff 上尾）
     取 `t = ε/σ²`，再对指数做实数代数 `−tε + t²σ²/2 = −ε²/(2σ²)`。
  5. `hoeffding_tail_independent_measure`（**合起来的完整尾界**）：把 3、4 复合，
     得到独立有界变量和 `S = ∑ X i` 的 `exp(−ε²/(2∑cᵢ²))` 尾界——与
     `RealRandomVerify.markov_bound` 的 `(1/ε)·∫f` 多项式界形成指数级提升，
     并对应 RealHoeffding.hoeffding_tail 的测度论版本。

**#check 结果（mathlib 4.14 实测）**：
- `ProbabilityTheory.iIndepFun.mgf_sum :
   iIndepFun (fun x => inferInstance) X μ → (∀ i, Measurable (X i)) →
   ∀ s : Finset ι, mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t`
  —— 独立性的 MGF 因子分解 mathlib **已有**，本文件不重证；
- `ProbabilityTheory.measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ]
   (ε : ℝ) (ht : 0 ≤ t) (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
   (μ {ω | ε ≤ X ω}).toReal ≤ exp (-t * ε) * mgf X μ t`（Chernoff 上尾）；
- `ProbabilityTheory.mgf`、`cgf`、`mgf_nonneg`、`mgf_pos`、`Real.exp_sum`；
- `MeasureTheory.Measure.pi`、`MeasureTheory.Measure.prod`、
  `MeasureTheory.integral_prod`（乘积测度 / Fubini 的备选路线）。

**诚实假设与降级（重要）**：
- 本文件的**独立性输入就是 mathlib 的 `iIndepFun`**（真正的测度论独立性），
  因子分解因此是既有定理的直接包装，而非有限计数 `Finset.prod_univ_sum`
  的手工版本。这是与 RealHoeffding 的分工：后者给有限空间的**完整自足**证明，
  本文件给测度论接口。
- **逐坐标「有界 + 均值为零 ⟹ mgf ≤ exp(t²cᵢ²/2)」这一 Hoeffding 引理，
  在一般测度论情形下本文件未重证**（mathlib 也没有该定理）：它以
  **显式假设** `hcoord`（定理 3、5 的 `c` 与 `ε/σ²` 处的 MGF 上界）进入。
  该引理的完整证明在有限计数设定下由 `RealHoeffding.hoeffding_lemma`
  （经 `RealAzuma.hoeffding_lemma_scaled` 缩放）给出；把有限计数结果搬到
  一般测度需要逐点弦不等式 `e^{λx} ≤ ((1−x)/2)e^{−λ} + ((1+x)/2)e^{λ}`
  的测度积分（`integral_mono` + `∫X = 0`），本文件**未做**，诚实标注。
  因此定理 4、5 的**逻辑地位是**：`MGF 界 ⟹ 尾界`（已被完整证明）；
  `独立 + 有界 + 零均值 ⟹ MGF 界`（外部输入 / 有限计数版）。
- `[IsFiniteMeasure μ]` 是 mathlib Chernoff 界的前提（保证 `(μ ·).toReal` 不出现
  `⊤`）；`σ² = ∑ cᵢ² > 0`、`ε > 0` 是尾界非退化前提。
- 可积性 `Integrable (fun ω => exp (t*S ω)) μ` 显式给出（不证可测性/可积性）。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ## 一、独立性 ⟹ MGF 因子分解（mathlib `iIndepFun.mgf_sum` 的接口包装） -/

/-- **MGF 因子分解（测度论版）**：有限指标集 `ι` 上 `iIndepFun` 的可测族 `X`，
其和的矩母函数等于各分量矩母函数之积。 -/
theorem mgf_factor_measure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*}
    [Fintype ι] {X : ι → Ω → ℝ}
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) (t : ℝ) :
    mgf (fun ω => ∑ i, X i ω) μ t = ∏ i, mgf (X i) μ t := by
  have h := hindep.mgf_sum hm (Finset.univ : Finset ι) (t := t)
  have hfun : (fun ω => ∑ i, X i ω) = (∑ i, X i) := by
    funext ω
    rw [Finset.sum_apply]
  rw [hfun]
  exact h

/-- `ι = Fin 2` 的具体情形：两独立变量之和的 MGF 是两 MGF 之积。 -/
theorem mgf_sum_pair {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Fin 2 → Ω → ℝ}
    (hindep : iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) (t : ℝ) :
    mgf (fun ω => X 0 ω + X 1 ω) μ t = mgf (X 0) μ t * mgf (X 1) μ t := by
  have h := mgf_factor_measure hindep hm t
  simpa [Fin.sum_univ_two, Fin.prod_univ_two] using h

/-! ## 二、逐坐标 MGF 界 ⟹ 和的 MGF 界 -/

/-- **逐坐标界合成**：若每个分量的 MGF 被 `exp(t²cᵢ²/2)` 控制，则和的 MGF
被 `exp(t²(∑cᵢ²)/2)` 控制。证明：因子分解 + `Finset.prod_le_prod`（用
`mgf_nonneg`）+ `Real.exp_sum` 合并 + 指数内代数。 -/
theorem mgf_bound_of_coordinate_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c : ι → ℝ} {t : ℝ}
    (hcoord : ∀ i, mgf (X i) μ t ≤ Real.exp (t ^ 2 * c i ^ 2 / 2)) :
    mgf (fun ω => ∑ i, X i ω) μ t ≤ Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 2) := by
  rw [mgf_factor_measure hindep hm t]
  calc ∏ i, mgf (X i) μ t
      ≤ ∏ i, Real.exp (t ^ 2 * c i ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hcoord i)
    _ = Real.exp (∑ i, t ^ 2 * c i ^ 2 / 2) := by rw [Real.exp_sum]
    _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 2) := by
        congr 1
        rw [Finset.mul_sum, Finset.sum_div]

/-! ## 三、测度版 Chernoff 桥：MGF 界 ⟹ 指数尾界 -/

/-- **测度版 Chernoff 桥（核心）**：`(μ {ε ≤ S}).toReal ≤ exp(−ε²/(2σ²))`，
由 mathlib 上尾 Chernoff 界 `measure_ge_le_exp_mul_mgf` 取 `t = ε/σ²` 得到。
指数内的代数：`−(ε/σ²)·ε + (ε/σ²)²·σ²/2 = −ε²/(2σ²)`。 -/
theorem hoeffding_tail_of_mgf_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {S : Ω → ℝ} {σ2 ε : ℝ} (hσ2 : 0 < σ2) (hε : 0 < ε)
    (h_int : Integrable (fun ω => Real.exp ((ε / σ2) * S ω)) μ)
    (h_mgf : mgf S μ (ε / σ2) ≤ Real.exp ((ε / σ2) ^ 2 * σ2 / 2)) :
    (μ {ω | ε ≤ S ω}).toReal ≤ Real.exp (-(ε ^ 2) / (2 * σ2)) := by
  have ht : 0 ≤ ε / σ2 := le_of_lt (div_pos hε hσ2)
  have hch := measure_ge_le_exp_mul_mgf (X := S) (μ := μ) (t := ε / σ2) ε ht h_int
  have hstep : Real.exp (-(ε / σ2) * ε) * mgf S μ (ε / σ2)
      ≤ Real.exp (-(ε / σ2) * ε) * Real.exp ((ε / σ2) ^ 2 * σ2 / 2) :=
    mul_le_mul_of_nonneg_left h_mgf (Real.exp_pos _).le
  have hexp : Real.exp (-(ε / σ2) * ε) * Real.exp ((ε / σ2) ^ 2 * σ2 / 2)
      = Real.exp (-(ε ^ 2) / (2 * σ2)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc (μ {ω | ε ≤ S ω}).toReal
      ≤ Real.exp (-(ε / σ2) * ε) * mgf S μ (ε / σ2) := hch
    _ ≤ Real.exp (-(ε / σ2) * ε) * Real.exp ((ε / σ2) ^ 2 * σ2 / 2) := hstep
    _ = Real.exp (-(ε ^ 2) / (2 * σ2)) := hexp

/-! ## 四、合起来：独立变量的完整指数尾界 -/

/-- **测度论 Hoeffding 尾界**：独立可测族、逐坐标 MGF 界（Hoeffding 引理的
输出形式）⟹ 和的指数尾界 `exp(−ε²/(2∑cᵢ²))`。 -/
theorem hoeffding_tail_independent_measure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c : ι → ℝ} {ε : ℝ}
    (hσ2 : 0 < ∑ i, c i ^ 2) (hε : 0 < ε)
    (hcoord : ∀ i, mgf (X i) μ (ε / (∑ i, c i ^ 2))
      ≤ Real.exp ((ε / (∑ i, c i ^ 2)) ^ 2 * c i ^ 2 / 2))
    (h_int : Integrable (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-(ε ^ 2) / (2 * (∑ i, c i ^ 2))) := by
  refine hoeffding_tail_of_mgf_bound (S := fun ω => ∑ i, X i ω) hσ2 hε h_int ?_
  exact mgf_bound_of_coordinate_bounds hindep hm hcoord

end Lattice
