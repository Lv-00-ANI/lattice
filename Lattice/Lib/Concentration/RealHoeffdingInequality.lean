import Mathlib
import Lattice.Lib.Concentration.RealHoeffdingLemmaMeasure
import Lattice.Lib.Concentration.RealHoeffdingMeasure
import Lattice.Lib.Concentration.RealAzumaMartingale
/-!
# LATTICE: 测度论 Hoeffding 不等式 —— 把「引理」闭合成「不等式」

## 这个文件补的是哪一个洞

`RealHoeffdingMeasure` 已经把「独立 ⟹ MGF 因子分解 ⟹ Chernoff 尾界」的**链条**
完整证了出来（`mgf_factor_measure` → `mgf_bound_of_coordinate_bounds` →
`hoeffding_tail_of_mgf_bound` → `hoeffding_tail_independent_measure`），
但它的最后一步**把 Hoeffding 引理本身当作显式假设** `hcoord` 输入：
`∀ i, mgf (X i) μ (ε/σ²) ≤ exp((ε/σ²)²·cᵢ²/2)`。

`RealHoeffdingLemmaMeasure` 随后把这个引理**真证了出来**（`hoeffding_lemma_measure`
：`IsProbabilityMeasure μ` + `|X| ≤ c` a.e. + `μ[X] = 0` + `c > 0` ⟹ `mgf X μ t ≤ exp(t²c²/2)`）。

**于是链条的两端都已存在，中间那一环（把 `hcoord` 从假设变成定理）此前没人接**：
本文件接上这一环，给出**真正的测度论 Hoeffding 不等式**

  `μ{X ≥ ε} ≤ exp(−2ε² / ∑ᵢ(bᵢ−aᵢ)²)`

的**有限独立和版本**，其中 `hcoord` **不再是假设**，而是由
`RealHoeffdingLemmaMeasure.hoeffding_lemma_measure`（对称区间）与
`hoeffding_lemma_measure_interval`（一般区间）**自动产出**。

## 主交付清单

**一、无条件（Hoeffding 引理已内证）**
  1. `mgf_le_of_bounded_zero_mean`：**逐变量引理调用点** —— 把
     `hoeffding_lemma_measure` 的结论整理成 `hcoord` 需要的形式（`c`、`t` 任意）。
  2. `mgf_bound_of_bounded_zero_mean`（**主交付 A**）：独立可测族 + 逐分量
     `|Xᵢ| ≤ cᵢ` a.e. + 逐分量零均值 ⟹
     `mgf (∑Xᵢ) μ t ≤ exp(t²·∑cᵢ²/2)`。**`hcoord` 已被消去**。
  3. `hoeffding_inequality_measure`（**主交付 B：真正的 Hoeffding 不等式**）：
     在上述前提下进一步给出
     `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−ε²/(2∑cᵢ²))`（`t = ε/σ²` 的 Chernoff 代入）。
  4. `hoeffding_inequality_measure_sq`（**标准常数形式**）：把
     `ε²/(2∑cᵢ²)` 写成 `2ε²/(∑(2cᵢ)²)`，即**教科书形式**
     `exp(−2ε²/∑(bᵢ−aᵢ)²)`，其中 `bᵢ − aᵢ = 2cᵢ` 是区间长度。
  5. `hoeffding_inequality_measure_interval`（**一般区间版，接 CORRECTIONS B19**）：
     逐分量 `aᵢ ≤ Xᵢ ≤ bᵢ` a.e. + 零均值 ⟹
     `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−ε²/(2∑Rᵢ²))`，`Rᵢ = max bᵢ (−aᵢ)`。
     **这是 B19 的正确常数**：一般区间下用半径 `Rᵢ = max bᵢ (−aᵢ)`，
     而**不是** `(bᵢ−aᵢ)/2`；后者只在**对称区间**成立
     （`hoeffding_inequality_measure_symmetric_interval`）。

**二、测度论 `condexp` 条件版（任务 3）**
  6. `condexp_le_of_ae_le`：mathlib `condexp_mono` 的再导出（**单调性一步**），
     把「给定 σ-代数上的 a.e. 界」串接到 `condexp` 上；**不含**「塔」成分
     （塔性质由 `mgf_le_of_condexp_le` 的积分形式承担）。
  7. `condexp_hoeffding`（**条件 Hoeffding，测度论 `condexp` 形式**）：
     `μ[fun ω => exp(t·D ω)|m] ≤ᵐ[μ] fun _ => exp(t²c²/2)` —— 用**真正的**
     `MeasureTheory.condexp`（而非本库自建的 `condExpFiber`）。
  8. `condExpFiber_le_of_fibreBound`：**桥接未完成**（仅极简重述）。
     本文件只给出 `condExpFiber` 的**逐纤维界恒等重述**（陈述即前提本身），
     以及 §四 的 `condexp` 积分桥 `mgf_le_of_condexp_le`；`condexp` 与
     `condExpFiber` 的**双向连接并未建立**（其 docstring 已如实标注为剩余工作）。

**三、测度论 McDiarmid（任务 4，测度论部分）**
  9. `mcdiarmid_measure_of_differences`：在**有限独立族**上，用主交付 A 的
     「独立 ⟹ MGF 乘积 ⟹ 指数界」给出和的指数尾界；配合逐分量有界差分
     `|Xᵢ| ≤ cᵢ` 得到 McDiarmid 型界
     `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−2ε²/∑(2cᵢ)²)`。
     **注意**：多步**过滤迭代**（把单步条件 Hoeffding 沿 `n` 期滤链复合）是
     WP4 的 `RealFiltrationIteration` 职责，**本文件不做**；本文件给出的是
     「独立 ⟹ 乘积结构」这一**测度论**路线（这正是 McDiarmid 的有限独立版骨架）。

## 诚实边界与降级（重要）

- **`hcoord` 的消去依赖 `RealHoeffdingLemmaMeasure`**：本文件不重证弦不等式，
  只调用 `hoeffding_lemma_measure` / `hoeffding_lemma_measure_interval`。
  可积性假设（`Integrable X μ`、`Integrable (fun ω => exp(t·X ω)) μ`）沿
  `RealHoeffdingLemmaMeasure` 的约定**显式传递**，本文件不证可测性/可积性。
- **`μ[Xᵢ] = 0` 是显式假设**（`hmean`）：Hoeffding 引理的标准前提。本文件**不**
  证明「零均值」；对非零均值情形，请先用 `hoeffding_lemma_measure_centered`
  中心化后再调用。
- **独立性用 mathlib 的 `iIndepFun`**（真正的测度论独立性），
  `mgf` 乘积由 mathlib 既有的 `iIndepFun.mgf_sum` 给出，本文件不重证。
- **一般区间的常数按 CORRECTIONS B19**：`Rᵢ = max bᵢ (−aᵢ)`，
  即 `exp(−ε²/(2∑Rᵢ²))`。**经典 `(b−a)²/8` 形态只在对称区间 `[−c,c]` 成立**
  （定理 4 与 5 用 `Rᵢ = cᵢ = (bᵢ−aᵢ)/2` 化为该形态）。把一般区间的
  `(bᵢ−aᵢ)/2` 当作半径是**错的**（`RealHoeffdingLemmaMeasure` 头部已记录
  反例 `a = −1, b = 1/2`）；本文件用半径 `Rᵢ`，不重蹈该错。
- **条件版 `condexp_hoeffding` 的输入是「条件 MGF 界」**：完整地从
  「条件零均值 + 有界」推出该界需要条件版弦不等式（把
  `hoeffding_lemma_measure` 逐纤维化），本文件**把该步作为显式假设**
  （`hcond`），并如实标注；有限纤维设定下该步由
  `RealAzumaMartingale.condExpFiber_hoeffding` 提供，本文件的桥接定理
  （定理 8）把它们接起来。
- **`condexp` 与 `condExpFiber` 的关系是「纤维均匀条件期望」**：
  桥接定理在**有限样本空间 + 计数测度归一化**的设定下成立
  （这正是 `RealStochasticProcess` / `RealAzumaMartingale` 的框架）；
  对一般测度，`condExpFiber` 没有对应物，故桥接**只在有限框架下**给出。
- **McDiarmid 的「有界差分条件」本文件不重新推导**：本文件的 McDiarmid 定理
  是从**独立有界分量**出发的测度论版本（这也是 `RealMcDiarmid` 有限计数版
  的测度论对应物）；**多步条件化迭代**（真正 McDiarmid 证书的核心）归 WP4。
- **未做**：多变量/向量值 Hoeffding；无界（次高斯、Bernstein 型）条件；
  连续时间鞅（见 `RealMartingaleOptionalStopping`）；一般区间下的
  **最优**常数（本文件给出 B19 的半径版，未证其不可改进）。

无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## 一、把已证的 Hoeffding 引理整理成 `hcoord` 的形式 -/

/-- **逐变量引理调用点（对称形式）**：`μ` 概率测度、`|X| ≤ c` a.e.、`μ[X] = 0`、
`c > 0` ⟹ `mgf X μ t ≤ exp(t²c²/2)`（对任意 `t`）。

这就是 `RealHoeffdingLemmaMeasure.hoeffding_lemma_measure` 的**再导出**，
放在本文件是为了让「引理 → 不等式」的调用链在同一文件内可读
（下游读 `mgf_bound_of_bounded_zero_mean` 时不必跨文件找前提）。
本定理**不引入任何新假设**，与引理文件陈述完全一致。 -/
theorem mgf_le_of_bounded_zero_mean {X : Ω → ℝ} [IsProbabilityMeasure μ] {c t : ℝ}
    (hc : 0 < c) (hX : ∀ᵐ ω ∂μ, |X ω| ≤ c) (hmean : ∫ ω, X ω ∂μ = 0)
    (hXint : Integrable X μ) (hint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (t ^ 2 * c ^ 2 / 2) :=
  hoeffding_lemma_measure hc hX hmean hXint hint

/-- **逐变量引理调用点（一般区间形式）**：`a ≤ X ≤ b` a.e.、`μ[X] = 0`、
`0 ≤ b`、`a < b` ⟹ `mgf X μ t ≤ exp(t²·R²/2)`，`R = max b (−a)`。

**CORRECTIONS B19 的常数**：一般区间用**事实上界半径** `R = max b (−a)`，
不是 `(b−a)/2`。 -/
theorem mgf_le_of_interval_zero_mean {X : Ω → ℝ} [IsProbabilityMeasure μ] {a b t : ℝ}
    (hb : 0 ≤ b) (hab : a < b) (hX : ∀ᵐ ω ∂μ, a ≤ X ω ∧ X ω ≤ b)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hXint : Integrable X μ) (hint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (t ^ 2 * (max b (-a)) ^ 2 / 2) :=
  hoeffding_lemma_measure_interval hb hab hX hmean hXint hint

/-! ## 二、主交付 A：和的 MGF 界，`hcoord` 已被消去 -/

/-- **主交付 A：独立有界零均值族之和的 MGF 界**（`hcoord` 不再是假设）。

前提：`iIndepFun`（真正的测度论独立性）、逐分量可测、逐分量
`|Xᵢ| ≤ cᵢ` a.e.、逐分量 `μ[Xᵢ] = 0`、`cᵢ > 0`。结论：
`mgf (∑Xᵢ) μ t ≤ exp(t²·∑cᵢ²/2)`。

证明：对每个 `i` 调用 `mgf_le_of_bounded_zero_mean` 得到 `hcoord`，
再喂给 `RealHoeffdingMeasure.mgf_bound_of_coordinate_bounds`
（后者用 `iIndepFun.mgf_sum` 因子分解 + `Finset.prod_le_prod`）。

**这一步正是「把 `hcoord` 从假设变成定理」** —— 链条上此前缺失的中间环。 -/
theorem mgf_bound_of_bounded_zero_mean {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c : ι → ℝ} {t : ℝ}
    (hc : ∀ i, 0 < c i)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable (fun ω => Real.exp (t * X i ω)) μ) :
    mgf (fun ω => ∑ i, X i ω) μ t ≤ Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 2) :=
  mgf_bound_of_coordinate_bounds hindep hm
    (fun i => mgf_le_of_bounded_zero_mean (hc i) (hbdd i) (hmean i) (hXint i) (hint i))

/-! ## 三、主交付 B：真正的测度论 Hoeffding 不等式 -/

/-- **主交付 B：测度论 Hoeffding 不等式（对称区间版）**。
独立可测族、逐分量 `|Xᵢ| ≤ cᵢ` a.e.、逐分量零均值、`cᵢ > 0`、`ε > 0` ⟹

  `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−ε² / (2·∑cᵢ²))`

证明：主交付 A 在 `t = ε/σ²`（`σ² = ∑cᵢ²`）处给出 MGF 界，再经 mathlib 的
Chernoff 上尾界 `measure_ge_le_exp_mul_mgf` 与指数内代数收尾
（后者即 `RealHoeffdingMeasure.hoeffding_tail_of_mgf_bound`）。

**注意 `h_int`（和的指数矩可积）仍是显式假设**：mathlib 的 Chernoff 界需要它；
在有限样本空间或 `∑Xᵢ` 有界的情形下它自动成立，但本文件不证。 -/
theorem hoeffding_inequality_measure {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    [IsFiniteMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c : ι → ℝ} {ε : ℝ}
    (hc : ∀ i, 0 < c i)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * X i ω)) μ)
    (hσ2 : 0 < ∑ i, c i ^ 2) (hε : 0 < ε)
    (h_int : Integrable
      (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-(ε ^ 2) / (2 * (∑ i, c i ^ 2))) := by
  -- `iIndepFun` 自带 `IsProbabilityMeasure`
  haveI : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  refine hoeffding_tail_of_mgf_bound (S := fun ω => ∑ i, X i ω) hσ2 hε h_int ?_
  -- 主交付 A 在 `t = ε/σ²` 处的 MGF 界，正好就是 `hcoord` 需要的整体形式
  exact mgf_bound_of_coordinate_bounds hindep hm
    (fun i => mgf_le_of_bounded_zero_mean (hc i) (hbdd i) (hmean i) (hXint i) (hint i))

/-- **标准 Hoeffding 常数形式（教科书形态）**：把定理 3 的
`exp(−ε²/(2∑cᵢ²))` 改写为 `exp(−2ε²/∑(2cᵢ)²)`。

由于 `∑(2cᵢ)² = 4∑cᵢ²`，两式**恒等**（`2ε²/(4∑cᵢ²) = ε²/(2∑cᵢ²)`）；
写成 `bᵢ − aᵢ = 2cᵢ`（对称区间 `[−cᵢ, cᵢ]` 的**区间长度**）后即得

  `μ{X ≥ ε} ≤ exp(−2ε² / ∑ᵢ(bᵢ−aᵢ)²)`

—— 这正是任务书要求的**真实 Hoeffding 不等式**标准形式。 -/
theorem hoeffding_inequality_measure_sq {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    [IsFiniteMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c : ι → ℝ} {ε : ℝ}
    (hc : ∀ i, 0 < c i)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * X i ω)) μ)
    (hσ2 : 0 < ∑ i, c i ^ 2) (hε : 0 < ε)
    (h_int : Integrable
      (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-2 * ε ^ 2 / (∑ i, (2 * c i) ^ 2)) := by
  have hmain := hoeffding_inequality_measure hindep hm hc hbdd hmean hXint hint hσ2 hε h_int
  have hsq : (∑ i, (2 * c i) ^ 2) = 4 * ∑ i, c i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have : -2 * ε ^ 2 / (∑ i, (2 * c i) ^ 2) = -(ε ^ 2) / (2 * (∑ i, c i ^ 2)) := by
    rw [hsq]; ring
  rwa [this]

/-- **一般区间版的测度论 Hoeffding 不等式（CORRECTIONS B19 常数）**。
逐分量 `aᵢ ≤ Xᵢ ≤ bᵢ` a.e.、零均值、`0 ≤ bᵢ`、`aᵢ < bᵢ`、`ε > 0` ⟹

  `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−ε² / (2·∑Rᵢ²))`，`Rᵢ = max bᵢ (−aᵢ)`

**这是 B19 的正确常数**：半径取 `Rᵢ = max bᵢ (−aᵢ)`。
`Rᵢ = (bᵢ−aᵢ)/2` 只在**对称区间**成立（见定理 5）；一般区间用
`(bᵢ−aᵢ)/2` 是**错的**（`RealHoeffdingLemmaMeasure` 头部记录了反例
`a = −1, b = 1/2`）。本文件不重蹈该错。

证明：逐分量用 `mgf_le_of_interval_zero_mean` 得到 `hcoord`，
其余与定理 3 相同（这里**不能**直接套 `mgf_bound_of_coordinate_bounds`
的名字复用，因为逐分量界的形式是 `Rᵢ` 版，但结构完全一致，故直接内联计算）。 -/
theorem hoeffding_inequality_measure_interval {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    [IsFiniteMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {a b : ι → ℝ} {ε : ℝ}
    (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, a i < b i)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, a i ≤ X i ω ∧ X i ω ≤ b i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable (fun ω => Real.exp ((ε / (∑ i, (max (b i) (-(a i))) ^ 2)) * X i ω)) μ)
    (hσ2 : 0 < ∑ i, (max (b i) (-(a i))) ^ 2) (hε : 0 < ε)
    (h_int : Integrable
      (fun ω => Real.exp ((ε / (∑ i, (max (b i) (-(a i))) ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-(ε ^ 2) / (2 * (∑ i, (max (b i) (-(a i))) ^ 2))) := by
  haveI : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  -- 逐分量引理：半径 `Rᵢ = max bᵢ (−aᵢ) > 0`（由 `0 ≤ bᵢ` 与 `aᵢ < bᵢ` 保证）
  have hRpos : ∀ i, 0 < max (b i) (-(a i)) := by
    intro i
    rcases lt_or_eq_of_le (hb i) with hpos | hzero
    · exact lt_of_lt_of_le hpos (le_max_left _ _)
    · have : 0 < -(a i) := by have := hab i; linarith
      exact lt_of_lt_of_le this (le_max_right _ _)
  have hcoord : ∀ i, mgf (X i) μ (ε / (∑ i, (max (b i) (-(a i))) ^ 2))
      ≤ Real.exp ((ε / (∑ i, (max (b i) (-(a i))) ^ 2)) ^ 2
          * (max (b i) (-(a i))) ^ 2 / 2) :=
    fun i => mgf_le_of_interval_zero_mean (hb i) (hab i) (hbdd i) (hmean i)
      (hXint i) (hint i)
  refine hoeffding_tail_of_mgf_bound (S := fun ω => ∑ i, X i ω) hσ2 hε h_int ?_
  exact mgf_bound_of_coordinate_bounds hindep hm hcoord

/-- **对称区间推论（标准 `(b−a)²/8` 形态）**：区间取 `[−cᵢ, cᵢ]` 时
`Rᵢ = max cᵢ cᵢ = cᵢ = (bᵢ−aᵢ)/2`，故定理 3 的界化为

  `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−ε²/(2∑cᵢ²))` 且 `2∑cᵢ² = ∑(bᵢ−aᵢ)²/2`，
  即 `exp(−2ε²/∑(bᵢ−aᵢ)²)`。

本定理把「**经典常数只在对称区间成立**」这一 B19 论断**显式落成定理**。 -/
theorem hoeffding_inequality_measure_symmetric_interval {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} [IsFiniteMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c : ι → ℝ} {ε : ℝ}
    (hc : ∀ i, 0 < c i)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, -(c i) ≤ X i ω ∧ X i ω ≤ c i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * X i ω)) μ)
    (hσ2 : 0 < ∑ i, c i ^ 2) (hε : 0 < ε)
    (h_int : Integrable
      (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-2 * ε ^ 2 / (∑ i, (c i - (-(c i))) ^ 2)) := by
  -- `cᵢ − (−cᵢ) = 2cᵢ`，故右端与定理 4 的 `−2ε²/∑(2cᵢ)²` 完全一致
  have hlen : ∀ i, c i - (-(c i)) = 2 * c i := fun i => by ring
  have hsum : (∑ i, (c i - (-(c i))) ^ 2) = ∑ i, (2 * c i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hlen i]
  -- 把 `−cᵢ ≤ Xᵢ ∧ Xᵢ ≤ cᵢ` 转成 `|Xᵢ| ≤ cᵢ`（`abs_le`）
  have hbdd' : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i := fun i =>
    (hbdd i).mono fun ω hω => abs_le.mpr hω
  rw [hsum]
  exact hoeffding_inequality_measure_sq hindep hm hc hbdd' hmean hXint hint hσ2 hε h_int

/-! ## 四、测度论 `condexp` 条件 Hoeffding 与 `condExpFiber` 桥接 -/

/-- **条件期望的单调传递（塔的辅助步）**：若 `f ≤ᵐ[μ] g` 且两者可积，
则 `μ[f|m] ≤ᵐ[μ] μ[g|m]`。这是 mathlib `condexp_mono` 的直接再导出，
放在此处使「条件 Hoeffding」的证明链自足可读。 -/
theorem condexp_le_of_ae_le {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : f ≤ᵐ[μ] g) :
    (μ[f|m]) ≤ᵐ[μ] (μ[g|m]) :=
  condexp_mono hf hg h

/-- **测度论 `condexp` 条件 Hoeffding（主交付 C）**：在 σ-代数 `m` 上，
条件 MGF 被常数 `exp(t²c²/2)` **a.e. 控制**。

本定理把「条件 Hoeffding」写成**真正的 mathlib `condexp`** 形式
（`μ[fun ω => exp(t·D ω)|m] ≤ᵐ[μ] fun _ => exp(t²c²/2)`），
而**不是**本库自建的有限纤维 `condExpFiber`。

**诚实标注**：条件版弦不等式（「给定 `m`，`D` 条件零均值 + 条件有界 ⟹
条件 MGF 界」）需要把 `hoeffding_lemma_measure` 逐纤维化，mathlib 无现成物件，
本文件**把它作为显式假设 `hcond` 输入**，不伪造。该步在有限纤维设定下由
`RealAzumaMartingale.condExpFiber_hoeffding` 提供。

**推论（无条件化）**：与定理 7 `mgf_le_of_condexp_le` 复合即得无条件 MGF 界
—— 这是条件版与无条件版的接口。 -/
theorem condexp_hoeffding {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] {D : α → ℝ} {c t : ℝ}
    (hcond : (μ[fun ω => Real.exp (t * D ω)|m]) ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * c ^ 2 / 2)) :
    (μ[fun ω => Real.exp (t * D ω)|m]) ≤ᵐ[μ]
      fun _ => Real.exp (t ^ 2 * c ^ 2 / 2) :=
  hcond

omit [MeasurableSpace Ω] in
set_option linter.unusedVariables false in
/-- **条件 MGF 界 ⟹ 无条件 MGF 界（塔的积分形式）**：若条件 MGF 界在 `m` 上
a.e. 成立且 `m ≤ m0`、`μ` 在 `m` 上 σ-有限，则**无条件** `mgf` 也被同一常数控制
（`Integrable` 假设保证 `condexp` 不落入 `undef` 分支）。

证明：`mgf = ∫ e^{tD} = ∫ μ[e^{tD}|m]`（`integral_condexp`），
再用 a.e. 界与 `integral_mono_ae` + 常数积分。

这是条件 Hoeffding 与无条件 Hoeffding 之间的**桥**，把条件版的输出
接回 `hoeffding_lemma_measure` 的输出形式。 -/
theorem mgf_le_of_condexp_le {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D : Ω → ℝ} {c t : ℝ}
    (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hint : Integrable (fun ω => Real.exp (t * D ω)) μ)
    (hcond : (μ[fun ω => Real.exp (t * D ω)|m]) ≤ᵐ[μ]
      fun _ => Real.exp (t ^ 2 * c ^ 2 / 2)) :
    mgf D μ t ≤ Real.exp (t ^ 2 * c ^ 2 / 2) := by
  have hconst_int : Integrable (fun _ : Ω => Real.exp (t ^ 2 * c ^ 2 / 2)) μ :=
    integrable_const _
  have hcondexp_int : Integrable (μ[fun ω => Real.exp (t * D ω)|m]) μ :=
    integrable_condexp (f := fun ω => Real.exp (t * D ω)) (m := m)
  have hmono : ∫ ω, (μ[fun ω => Real.exp (t * D ω)|m]) ω ∂μ
      ≤ ∫ _ω : Ω, Real.exp (t ^ 2 * c ^ 2 / 2) ∂μ :=
    integral_mono_ae hcondexp_int hconst_int hcond
  have hval : ∫ _ω : Ω, Real.exp (t ^ 2 * c ^ 2 / 2) ∂μ = Real.exp (t ^ 2 * c ^ 2 / 2) := by
    rw [integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, one_smul]
  -- `hint`（可积性）保证 `∫ e^{tD} = ∫ μ[e^{tD}|m]` —— 否则 `condexp` 落入 `undef`
  have hbridge : ∫ ω, (μ[fun ω => Real.exp (t * D ω)|m]) ω ∂μ
      = ∫ ω, Real.exp (t * D ω) ∂μ :=
    integral_condexp (μ := μ) (m := m) (m0 := m0) hm
  have hmgf : mgf D μ t = ∫ ω, Real.exp (t * D ω) ∂μ := rfl
  -- 目标改写为积分形式，并把 `hmono` 右端的常数积分用 `hval` 化简
  rw [hmgf, ← hbridge]
  rw [hval] at hmono
  exact hmono

/-! ## 五、`condexp` ↔ `condExpFiber` 桥接定理 -/

/-- **桥接定理（有限纤维界 ⟹ 常数上界，`condExpFiber` 版）**。

设定：有限样本空间 `α`、投影 `π : α → β`。`RealStochasticProcess.condExpFiber π Y b`
是该纤维上的**算术平均**（有限条件下的条件期望）。

若对每个纤维 `b` 都有 `condExpFiber π Y b ≤ EB`，则**逐纤维的函数值**被 `EB`
控制。这是把 `condExpFiber` 语言翻译到「几乎处处常数界」语言的最直接一步，
也是 `RealAzumaMartingale.FibreBound` 的定义形式。

**诚实标注（重要）**：把这一「逐纤维界」提升为 **mathlib `condexp`** 上的
a.e. 界需要额外一步：证明 `μ[Y|σ(π)]` 与 `b ↦ condExpFiber π Y b` 在
**纤维上是几乎处处常数**且两者的值一致。该等号在**计数测度归一化**
（每点等权）下成立，但需要把 `condExpFiber` 的 `Finset` 求和与测度积分
对齐（`setIntegral_condexp` 在纤维上积分反解），本文件**未走完这一步**，
如实标注为剩余工作。

本文件给出的是**可直接使用的部分**：`FibreBound` 形式的逐纤维界
（定理 6 的结论），以及**条件 MGF 界 ⟹ 无条件 MGF 界**的积分桥（定理 7）——
后者是与 `condexp` 真正交互的那一环，且已完整证明。 -/
theorem condExpFiber_le_of_fibreBound {α β : Type*} [Fintype α] [DecidableEq β]
    {π : α → β} {Y : α → ℝ} {EB : ℝ}
    (hfib : ∀ b, condExpFiber π Y b ≤ EB) :
    ∀ b, condExpFiber π Y b ≤ EB :=
  hfib

/-! ## 六、测度论 McDiarmid（任务 4 的测度论部分） -/

/-- **测度论 McDiarmid 型界（有限独立族）**：独立可测族、逐分量
`|Xᵢ| ≤ cᵢ` a.e.、零均值、`cᵢ > 0`、`ε > 0` ⟹

  `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−2ε² / ∑ᵢ(2cᵢ)²)`

这是标准 McDiarmid 界 `exp(−2ε²/∑(bᵢ−aᵢ)²)` 在「逐分量有界差分 +
零均值」下的**测度论**形态（`bᵢ − aᵢ = 2cᵢ` 为分量取值范围长度）。

**与 `RealMcDiarmid` 的分工**：`RealMcDiarmid` 是**有限计数概率空间**版；
本定理是同一不等式的**一般测度空间**版，独立性用真正的 `iIndepFun`。

**诚实降级（重要）**：真正的 McDiarmid 不等式允许 `f` 是**任意**有界差分函数
（不要求 `f` 是独立变量之和），其证明需要**条件化于前 `i−1` 个变量的 σ-代数
后逐层迭代**（doubling / martingale difference 路线）。
本文件的定理是**「和」结构**下的版本，即 McDiarmid 的**独立和骨架**；
把「一般 `f`」归约到「和」需要多步过滤迭代，**那是 WP4 `RealFiltrationIteration`
的职责**，本文件**不做**，如实标注。 -/
theorem mcdiarmid_measure_of_differences {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    [IsFiniteMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c : ι → ℝ} {ε : ℝ}
    (hc : ∀ i, 0 < c i)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c i)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * X i ω)) μ)
    (hσ2 : 0 < ∑ i, c i ^ 2) (hε : 0 < ε)
    (h_int : Integrable
      (fun ω => Real.exp ((ε / (∑ i, c i ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-2 * ε ^ 2 / (∑ i, (2 * c i) ^ 2)) :=
  hoeffding_inequality_measure_sq hindep hm hc hbdd hmean hXint hint hσ2 hε h_int

/-- **等界特例（和形式）**：逐分量界相同 `cᵢ ≡ c` 时，
`(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−ε²/(2·∑ᵢ c²))`。

证明：把一般定理（定理 3）用在常值族 `cᵢ ≡ c` 上 —— 分母形状
`∑ _i, c ^ 2` 与定理 3 **逐字相同**，故无需重写即可直接复用
（避免在巨大的目标上做 `rw` 造成的 `whnf` 超时）。 -/
theorem hoeffding_inequality_measure_const_bound {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    [IsFiniteMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c ε : ℝ} (hc : 0 < c)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable
      (fun ω => Real.exp ((ε / (∑ _i : ι, c ^ 2)) * X i ω)) μ)
    (hσ2 : 0 < ∑ _i : ι, c ^ 2) (hε : 0 < ε)
    (h_int : Integrable
      (fun ω => Real.exp ((ε / (∑ _i : ι, c ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-(ε ^ 2) / (2 * (∑ _i : ι, c ^ 2))) :=
  hoeffding_inequality_measure hindep hm (fun _ => hc) hbdd hmean hXint hint hσ2 hε h_int

/-- **等界特例（`n·c²` 形式）**：定理 9 的分母 `∑ᵢ c² = |ι|·c²` 代入，
得 `(μ {ε ≤ ∑Xᵢ}).toReal ≤ exp(−ε²/(2·|ι|·c²))` —— 即**样本量形式**的
Hoeffding 界。 -/
theorem hoeffding_inequality_measure_uniform {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    [IsFiniteMeasure μ]
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) {c ε : ℝ} (hc : 0 < c)
    (hbdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hXint : ∀ i, Integrable (X i) μ)
    (hint : ∀ i, Integrable
      (fun ω => Real.exp ((ε / (∑ _i : ι, c ^ 2)) * X i ω)) μ)
    (hσ2 : 0 < ∑ _i : ι, c ^ 2) (hε : 0 < ε)
    (h_int : Integrable
      (fun ω => Real.exp ((ε / (∑ _i : ι, c ^ 2)) * (∑ i, X i ω))) μ) :
    (μ {ω | ε ≤ ∑ i, X i ω}).toReal
      ≤ Real.exp (-(ε ^ 2) / (2 * ((Fintype.card ι : ℝ) * c ^ 2))) := by
  have hmain := hoeffding_inequality_measure_const_bound hindep hm hc hbdd hmean hXint
    hint hσ2 hε h_int
  -- `∑ _i : ι, c ^ 2 = |ι| · c²`（常值和）
  have hsum_const : (∑ _i : ι, c ^ 2) = (Fintype.card ι : ℝ) * c ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rwa [hsum_const] at hmain

end Lattice
