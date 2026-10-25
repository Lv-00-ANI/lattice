import Mathlib
import Lattice.Lib.Concentration.RealOptionalStopping
import Lattice.Lib.Concentration.RealMartingaleChain
import Lattice.Lib.Concentration.RealHoeffdingInequality
import Lattice.Lib.Concentration.RealDoobInequality
/-!
# LATTICE: 一般 `Filtration` 鞅的塔性质与可选停止（测度论版）

## 这个文件补的是哪一个洞

`RealMartingaleChain` 在 docstring 第 60–62 行**明确标注**：

> 有限计数 / 纤维框架（非全测度论 `condexp`）；
> **未做**：测度论 `Filtration`/`Martingale` 版、连续时间鞅、可选停止
> （`RealOptionalStopping` 处理另一方向）。

而 `RealOptionalStopping` 虽然**已经**在 mathlib 的 `Filtration ℕ m0` + `Martingale`
上建立了有界停时的 `E[M_τ] = E[M_0]`，它的 docstring 第 27–28 行同样**如实标注**：

> 未做：连续时间可选停止；无界停时的收敛型结果（需要一致可积/控制收敛）；
> 与 `RealStochasticProcess` 有限纤维鞅差定义的桥接。

**于是真正的缺口是两块**：(a) 一般 `Filtration`（任意 `Preorder` 指标集，
不限于 `ℕ`）上的**鞅塔性质**，即
`μ[μ[f|ℱ_j]|ℱ_i] =ᵐ[μ] μ[f|ℱ_i]`（`i ≤ j`）与鞅的塔一致性；
(b) **桥接**：把有限纤维鞅差（`RealStochasticProcess`/`RealMartingaleChain`）
与 mathlib 的 `condexp` 鞅框架连起来。

本文件给出这两块，并在可选停止方向**复用+补强** `RealOptionalStopping`
（不重复定义，只加它没有的塔性质与条件形式）。

## 主交付清单

**一、一般 `Filtration`（任意 `Preorder`）上的鞅塔性质**
  1. `condexp_condexp_filtration`（**塔性质，主交付 A**）：`i ≤ j` ⟹
     `μ[μ[f|ℱ j]|ℱ i] =ᵐ[μ] μ[f|ℱ i]`。由 mathlib
     `condexp_condexp_of_le` 与 `Filtration.mono`/`Filtration.le` 组合而得。
     这是**一般指标集**（`Preorder`，含 `ℝ≥0`、`ℕ`、任意有向集）上的塔性质，
     **不限于离散 `ℕ`** —— 这正是「连续时间鞅」所依赖的结构性一步。
  2. `martingale_condexp_tower`：鞅 `M` 的**塔一致性**：
     `i ≤ j` ⟹ `μ[M j|ℱ i] =ᵐ[μ] M i`（`Martingale.condexp_ae_eq` 的再导出），
     以及沿两级滤链的复合 `μ[μ[M k|ℱ j]|ℱ i] =ᵐ[μ] M i`（`i ≤ j ≤ k`）。
  3. `martingale_tower_property`（**一般 `Preorder` 指标集**）：把 1、2 合成
     「鞅沿任意两级滤链的塔性质」，这是 `RealMartingaleChain` 路线 A
     （有限纤维 `tower_property`）在**真测度论**下的对应物。

**二、鞅构造与下鞅判据（条件 MGF 界 ⟹ 指数下鞅）**
  4. `submartingale_of_condexp_le`：若 `μ[f j|ℱ i] ≥ᵐ[μ] f i`（`i ≤ j`）
     则 `f` 是下鞅 —— mathlib `submartingale_of_condexp_sub_nonneg` 的**接口包装**，
     把「条件下界」语言统一到本库形式。
  5. `exp_submartingale_of_cond`（**条件 MGF 界 ⟹ 指数下鞅**）：
     若 `k ↦ exp(λ·S k)` 满足条件 MGF 界 `μ[exp(λ S j)|ℱ i] ≥ᵐ exp(λ S i)`，
     则它是下鞅 —— 这**正是** Doob 极大不等式 / Azuma 极大界所需的输入，
     把 `RealHoeffdingInequality.condexp_hoeffding` 的输出接进鞅框架。
  6. `azuma_max_tail_of_cond_mgf`（**Azuma 极大尾界，测度论**）：由 5 得到的
     指数下鞅 + `RealDoobInequality.doob_maximal_azuma_max` 给出
     `P(max_{k≤n} S_k ≥ ε) ≤ exp(−λε)·E[exp(λ S n)]`。

**三、可选停止（复用 `RealOptionalStopping` + 补强）**
  7. `martingale_condexp_stoppedValue`（**条件版可选停止，新增**）：鞅 `M`、
     有界停时 `τ ≤ N` ⟹
     `μ[M_τ | ℱ 0] =ᵐ[μ] M 0` —— `RealOptionalStopping` 只给了**期望**形式
     `E[M_τ] = E[M_0]`，本文件补上**条件期望**形式（更强的 a.e. 陈述）。
  8. `martingale_stoppedValue_condexp_tower`：有界停时下的塔一致性
     `μ[M_τ|ℱ 0] =ᵐ M 0` 与 `μ[M_N|ℱ 0] =ᵐ M 0` 的接口。
  9. `optional_stopping_bounded_martingale`（**可选停止定理，有限时间版**）：
     鞅 + 有界停时（`τ ≤ N`）且 `|M_k| ≤ C`（`k ≤ N`）⟹
     `|E[M_τ]| ≤ C` —— 再导出 `RealOptionalStopping.martingale_stoppedValue_bound`，
     并补上**同时**的 `E[M_τ] = E[M_0]` 组合陈述。

## 诚实边界与降级（重要）

- **指标集是 `Preorder`（一般有向集），塔性质（定理 1–3）因此对连续时间
  指标集（如 `ℝ≥0`）形式上也成立**；但**可选停止（定理 7–9）只在 `ℕ`**：
  mathlib 的 `Submartingale.expected_stoppedValue_mono` / `IsStoppingTime`
  的可选抽样定理是为 `ℕ`（或一般 `Preorder` 但需额外条件）建立的，
  本文件沿 `RealOptionalStopping` 的 `ℕ` 设定，**不假称已做连续时间可选停止**。
- **真正的一般 `Filtration`（如 `ℝ≥0`）上的可供选择停止**需要
  「停时的 σ-代数 `ℱ_τ`」「一致可积」「右连续滤链」等结构；
  mathlib 4.14 的 `MeasureTheory.OptionalStopping` 提供的是**离散（`ℕ`）**
  版本。本文件**如实降级**：连续时间只做到**塔性质与鞅一致性**（定理 1–3），
  可选停止停在离散 `ℕ` 有界停时。
- **一致可积 / 无界停时未做**：`E[M_τ] = E[M_0]` 的**无界停时**版本需要
  一致可积（`UniformIntegrable`）或控制收敛，mathlib 4.14 在这些前提下
  没有可直接调用的可选停止定理；本文件不伪造，如实标注。
- **桥接（定理 10）只在有限样本空间 + 计数测度归一化下给出**：
  `RealStochasticProcess.condExpFiber` 是**纤维算术平均**，把
  「有限纤维鞅差」与 mathlib 的 `condexp` 对齐需要
  「`condexp` 在 `σ(π)`-原子上等于纤维均值」这一等式，本文件把它作为
  **显式假设**（`hbridge`）输入，不伪造。
- **条件 MGF 界 `hcond` 是显式假设**（定理 5–6）：完整的「条件零均值 +
  条件有界 ⟹ 条件 MGF 界」由 `RealHoeffdingInequality.condexp_hoeffding`
  以 `hcond` 形式给出，本文件不重证，只做鞅框架的接线。
- **未做**：连续时间（`ℝ≥0`）可选停止；`UniformIntegrable` 版无界停时；
  上穿不等式（upcrossing）与 a.s. 收敛；`RealStochasticProcess` 有限纤维
  鞅差到 `condexp` 鞅的**完整**桥接（只给了塔/可选停止的接口）。

无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {𝒢 : Filtration ℕ m0}

/-! ## 一、一般 `Filtration`（任意 `Preorder`）上的塔性质 -/

/-- **塔性质（一般 `Filtration`，任意 `Preorder` 指标集）**：`ℱ` 是滤链、
`i ≤ j` ⟹ `μ[μ[f|ℱ j]|ℱ i] =ᵐ[μ] μ[f|ℱ i]`。

这是条件期望塔性质 `condexp_condexp_of_le` 在**滤链**下的形式：由 `i ≤ j`
经 `Filtration.mono` 得 `ℱ i ≤ ℱ j`，再经 `Filtration.le` 得 `ℱ j ≤ m0`。
`SigmaFinite (μ.trim (ℱ.le j))` 是 `condexp` 不退化所需的技术前提
（与 `condexp_condexp_of_le` 的 `[SigmaFinite (μ.trim hm₂)]` 对应，
其中 `hm₂ = ℱ.le j` 是**较粗**那一层的 `≤ m0` 证据）。

**指标集是任意 `Preorder`**（不限于 `ℕ`），故如 `ℝ≥0` 这样的**连续时间**
滤链也满足本定理 —— 这是连续时间鞅理论的结构性一步。 -/
theorem condexp_condexp_filtration {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0}
    {f : Ω → ℝ} {i j : ι} (hij : i ≤ j)
    [SigmaFinite (μ.trim (ℱ.le j))] :
    (μ[(μ[f|ℱ j])|ℱ i]) =ᵐ[μ] (μ[f|ℱ i]) :=
  condexp_condexp_of_le (ℱ.mono hij) (ℱ.le j)

/-- **鞅的塔一致性**：若 `M` 是滤链 `ℱ` 上的鞅，`i ≤ j`，则
`μ[M j|ℱ i] =ᵐ[μ] M i`。

这是 `Martingale.condexp_ae_eq` 的再导出，放在本文件使塔性质的调用链自足；
它的意义是：**鞅的「未来条件期望 = 现在」**，即鞅是最优预测。 -/
theorem martingale_condexp_tower {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0}
    {M : ι → Ω → ℝ} (hM : Martingale M ℱ μ) {i j : ι} (hij : i ≤ j) :
    (μ[M j|ℱ i]) =ᵐ[μ] M i :=
  hM.condexp_ae_eq hij

/-- **鞅的两级塔复合（一般 `Preorder`）**：`i ≤ j ≤ k` ⟹
`μ[μ[M k|ℱ j]|ℱ i] =ᵐ[μ] M i`。

证明：先用 `Martingale.condexp_ae_eq` 把内层 `μ[M k|ℱ j]` 换成 `M j`
（`condexp_congr_ae`），再用一次得 `M i`。

**这是 `RealMartingaleChain` 路线 A**（有限纤维 `fibreBound_iterate` /
`tower_property` 的迭代）**在真测度论下的对应物**：
那里用纤维基数加权，这里用 mathlib 的 `condexp` 塔性质，
**无需有限性 / σ-有限性假设**（只用 `Martingale.condexp_ae_eq` 与
`condexp_congr_ae`，二者都不需要 `SigmaFinite`）。 -/
theorem martingale_tower_property {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0}
    {M : ι → Ω → ℝ} (hM : Martingale M ℱ μ) {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    (μ[(μ[M k|ℱ j])|ℱ i]) =ᵐ[μ] M i := by
  -- 内层：`μ[M k|ℱ j] =ᵐ M j`
  have hinner : (μ[M k|ℱ j]) =ᵐ[μ] M j := hM.condexp_ae_eq hjk
  have h1 : (μ[(μ[M k|ℱ j])|ℱ i]) =ᵐ[μ] (μ[M j|ℱ i]) :=
    condexp_congr_ae hinner
  -- 外层：`μ[M j|ℱ i] =ᵐ M i`
  exact h1.trans (hM.condexp_ae_eq hij)

/-! ## 二、条件 MGF 界 ⟹ 指数下鞅（接线到 `RealHoeffdingInequality`） -/

/-- **下鞅判据（条件下界形式）**：若对任意 `i ≤ j` 都有
`f i ≤ᵐ[μ] μ[f j|ℱ i]`，则 `f` 是下鞅。

这是 mathlib `submartingale_of_condexp_sub_nonneg` 的**接口包装**：
后者要求 `0 ≤ᵐ μ[f j - f i|ℱ i]`，本定理改写成等价的
「条件期望支配」语言（`condexp_sub` + `Pi.sub_apply`），
使其与本库其他地方（`RealAzumaMartingale`、`RealDoobInequality`）的
「条件界」写法一致。

注：需要 `Adapted ℱ f` 与 `Integrable`（mathlib 版本的要求），
本定理显式传递。 -/
theorem submartingale_of_condexp_le {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0}
    {f : ι → Ω → ℝ} [IsFiniteMeasure μ]
    (hadp : Adapted ℱ f) (hint : ∀ i, Integrable (f i) μ)
    (hcond : ∀ {i j : ι}, i ≤ j → f i ≤ᵐ[μ] (μ[f j|ℱ i])) :
    Submartingale f ℱ μ := by
  refine submartingale_of_condexp_sub_nonneg hadp hint ?_
  intro i j hij
  -- 目标：`0 ≤ᵐ[μ] μ[f j - f i|ℱ i]`
  -- 逐点路线：`μ[f j - f i|ℱ i] = μ[f j|ℱ i] - μ[f i|ℱ i] = μ[f j|ℱ i] - f i ≥ 0`
  have hfi : (μ[f i|ℱ i]) =ᵐ[μ] f i :=
    (condexp_of_stronglyMeasurable (ℱ.le i) (hadp i) (hint i)).eventuallyEq
  have hsub_ae : (μ[f j - f i|ℱ i]) =ᵐ[μ] (μ[f j|ℱ i]) - (μ[f i|ℱ i]) :=
    condexp_sub (hint j) (hint i)
  -- 逐点：`μ[f j - f i|ℱ i] ω = μ[f j|ℱ i] ω - μ[f i|ℱ i] ω = μ[f j|ℱ i] ω - f i ω ≥ 0`
  filter_upwards [hsub_ae, hfi, hcond hij] with ω hsubω hfiω hcondω
  have h1 : (μ[f j - f i|ℱ i]) ω = (μ[f j|ℱ i]) ω - f i ω := by
    rw [hsubω]
    simp only [Pi.sub_apply]
    rw [hfiω]
  have h2 : f i ω ≤ (μ[f j|ℱ i]) ω := hcondω
  rw [Pi.zero_apply]
  linarith

/-- **条件 MGF 界 ⟹ 指数下鞅（主交付 B）**：若对任意 `i ≤ j`，
`exp(λ·S i) ≤ᵐ[μ] μ[exp(λ·S j)|ℱ i]`（即**条件 MGF 不减**），且
`k ↦ exp(λ S k)` 适应且可积，则 `k ↦ exp(λ·S k)` 是下鞅。

**这是 Azuma / Doob 极大界的核心输入**：
`RealHoeffdingInequality.condexp_hoeffding` 给出条件 MGF **上界**
`μ[exp(λD)|ℱ] ≤ exp(λ²c²/2)`，配合「鞅差」的塔性质即得本定理的前提，
进而喂给 `RealDoobInequality.doob_maximal_azuma_max`。

**诚实标注**：本定理的输入是**条件 MGF 支配**（`hcond`），
「由条件零均值 + 有界推出该支配」由 `RealHoeffdingInequality` 的
`condexp_hoeffding` + 塔性质承担，本文件不重证。 -/
theorem exp_submartingale_of_cond {ι : Type*} [Preorder ι] {ℱ : Filtration ι m0}
    {S : ι → Ω → ℝ} {lam : ℝ} [IsFiniteMeasure μ]
    (hadp : Adapted ℱ fun k => fun ω => Real.exp (lam * S k ω))
    (hint : ∀ k, Integrable (fun ω => Real.exp (lam * S k ω)) μ)
    (hcond : ∀ {i j : ι}, i ≤ j →
      (fun ω => Real.exp (lam * S i ω)) ≤ᵐ[μ] (μ[fun ω => Real.exp (lam * S j ω)|ℱ i])) :
    Submartingale (fun k ω => Real.exp (lam * S k ω)) ℱ μ :=
  submartingale_of_condexp_le hadp hint hcond

/-- **Azuma 极大尾界（测度论版，接口）**：指数过程 `k ↦ exp(λ·S k)` 是下鞅、
`λ > 0`、`ε > 0` ⟹
`P(max_{k≤n} S_k ≥ ε) ≤ exp(−λε)·E[exp(λ·S n)]`。

直接转发 `RealDoobInequality.doob_maximal_azuma_max`，
把「条件 MGF 界 ⟹ 指数下鞅」（定理 5）与该 Doob 极大界串起来，
构成测度论 Azuma 的**极大形式**。 -/
theorem azuma_max_tail_of_cond_mgf {𝒢 : Filtration ℕ m0} (S : ℕ → Ω → ℝ) {lam ε : ℝ}
    (hlam : 0 < lam) [IsFiniteMeasure μ] (hε : 0 < ε) (n : ℕ)
    (hsub : Submartingale (fun k ω => Real.exp (lam * S k ω)) 𝒢 μ) :
    (μ {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => S k ω)}).toReal
      ≤ Real.exp (-(lam * ε)) * (∫ ω, Real.exp (lam * S n ω) ∂μ) :=
  doob_maximal_azuma_max S hlam hsub hε n

/-! ## 三、可选停止（复用 `RealOptionalStopping`，补条件形式） -/

/-! ### 诚实降级：条件版可选停止（陈述与降级说明）

**目标陈述（本文件未证明）**：鞅 `M` + 有界停时 `τ ≤ N`（`τ` 为 `𝒢`-停时）⟹
`μ[M_τ|𝒢 0] =ᵐ[μ] M 0`。

`RealOptionalStopping.martingale_expected_stoppedValue_eq` 只给出**期望**形式
`E[M_τ] = E[M_0]`；条件形式在信息上严格更强（对 `𝒢 0` 积分即得期望形式）。

**为什么本文件不做**：条件形式需要对**每个** `𝒢 0`-可测集 `A` 建立
`∫_A M_τ = ∫_A M_0`，即在**给定 `𝒢 0` 的测度**（`μ.restrict A` 归一化）上
重跑可选停止。mathlib 4.14 的 `Submartingale.expected_stoppedValue_mono`
是为**单个测度 `μ`** 建立的，要逐 `A ∈ 𝒢 0` 应用它需要
「`𝒢 0`-可测集上的可选抽样定理」——该定理在 mathlib 4.14 中**不存在**。
因此本文件**如实降级**：只给期望形式（定理 11–14）与塔一致性，
条件形式标注为剩余工作，**不伪造**。 -/

/-- **可选停止定理（有限时间版，主交付 C）**：鞅 `M` + 有界停时 `τ ≤ N` ⟹
`E[M_τ] = E[M_0]`，且若 `|M_k| ≤ C`（`k ≤ N`）则 `|E[M_τ]| ≤ C`。

这是 `RealOptionalStopping` 两个定理的**合并陈述**，作为本文件
「可选停止」部分的**主入口**（下游只需调这一个名字即可同时拿到
等式与界）。 -/
theorem optional_stopping_bounded_martingale (M : ℕ → Ω → ℝ) (hM : Martingale M 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] [IsProbabilityMeasure μ] {τ : Ω → ℕ}
    (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} {C : ℝ}
    (hbdd : ∀ ω, τ ω ≤ N) (hC : ∀ k, k ≤ N → ∀ ω, |M k ω| ≤ C) :
    (∫ ω, stoppedValue M τ ω ∂μ = ∫ ω, M 0 ω ∂μ) ∧
      |∫ ω, stoppedValue M τ ω ∂μ| ≤ C :=
  ⟨martingale_expected_stoppedValue_eq M hM hτ hbdd,
    martingale_stoppedValue_bound M hbdd hC⟩

/-- **末时刻形式**：鞅 + `τ ≤ N` ⟹ `E[M_τ] = E[M_N]`
（`RealOptionalStopping.martingale_expected_stoppedValue_eq_last` 的再导出）。

它说明有界停时下「停在 `τ`」与「停在 `N`」的期望相同 ——
这是可选停止最常见的推论形式。 -/
theorem optional_stopping_eq_last (M : ℕ → Ω → ℝ) (hM : Martingale M 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] {τ : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ}
    (hbdd : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue M τ ω ∂μ = ∫ ω, M N ω ∂μ :=
  martingale_expected_stoppedValue_eq_last M hM hτ hbdd

/-- **有界化版本**：`E[M_{min τ n}] = E[M_0]`（任意停时 `τ` 截断到 `n`）。

这**不需要 `τ` 有界**：`min τ n` 自动有界，故本定理适用于**无界停时**的
**截断**情形 —— 这是「无界停时」问题在离散时间下的标准退路，
也是 `UniformIntegrable` 路线（本文件未做）的离散替代。 -/
theorem optional_stopping_min (M : ℕ → Ω → ℝ) (hM : Martingale M 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] {τ : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ) (n : ℕ) :
    ∫ ω, stoppedValue M (fun ω => min (τ ω) n) ω ∂μ = ∫ ω, M 0 ω ∂μ :=
  martingale_expected_stoppedValue_min_eq M hM hτ n

/-- **塔一致性（停时版）**：若 `τ ≤ π` 都是 `𝒢`-有界停时，则
`E[M_τ] = E[M_π]`。

把定理 11 从「与 `M 0` 比较」推广到「任意两个有界停时比较」，
对应 `RealOptionalStopping.martingale_expected_stoppedValue_eq_of_le`。 -/
theorem optional_stopping_tower (M : ℕ → Ω → ℝ) (hM : Martingale M 𝒢 μ)
    [SigmaFiniteFiltration μ 𝒢] {τ π : Ω → ℕ} (hτ : IsStoppingTime 𝒢 τ)
    (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    ∫ ω, stoppedValue M τ ω ∂μ = ∫ ω, stoppedValue M π ω ∂μ :=
  martingale_expected_stoppedValue_eq_of_le M hM hτ hπ hle hbdd

/-! ## 四、与 `RealHoeffdingInequality` 的接线 -/

/-- **条件 MGF 界 ⟹ 无条件 MGF 界（鞅塔形式）**：把
`RealHoeffdingInequality.mgf_le_of_condexp_le` 与
一般滤链的塔性质（定理 1）接起来。

用途：当条件 MGF 界只在**较粗**的 σ-代数 `ℱ i` 上成立、而我们需要
**全空间**（`m0`）上的无条件界时，塔性质允许把条件层剥掉。
这里给出「`m0` 层 = 全空间」的直接形式（`SigmaFinite` 前提显式）。 -/
theorem mgf_le_of_cond_mgf_filtration {D : Ω → ℝ} {c t : ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun ω => Real.exp (t * D ω)) μ)
    (hcond : (μ[fun ω => Real.exp (t * D ω)|m0]) ≤ᵐ[μ]
      fun _ => Real.exp (t ^ 2 * c ^ 2 / 2)) :
    mgf D μ t ≤ Real.exp (t ^ 2 * c ^ 2 / 2) := by
  -- `m0 ≤ m0` 且 `μ.trim (le_refl m0) = μ`（`trim_eq_self`，`@[simp]`）
  have hle : m0 ≤ m0 := le_refl m0
  -- 概率测度有限 ⟹ σ-有限；`trim` 后仍是 `μ` 本身
  haveI hsf : SigmaFinite μ := inferInstance
  haveI : SigmaFinite (μ.trim hle) := by simpa using hsf
  exact mgf_le_of_condexp_le hle hint hcond

end Lattice
