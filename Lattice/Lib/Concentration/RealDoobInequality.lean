import Mathlib

/-!
# LATTICE: Doob 极大不等式（离散有限版）与鞅版 Azuma 的极大形式

在 mathlib 的离散鞅框架上建立 Doob 极大不等式，并把它接到指数鞅上，
给出**鞅版 Azuma 的极大不等式形式**。

主要结果：

  1. `doob_maximal_ineq`（`ε : ℝ≥0` 版）：非负下鞅 `f`，`ε • μ{ε ≤ max_{k≤n} f_k} ≤
     ∫_{ε ≤ max} f_n dμ`（直接包装 mathlib `MeasureTheory.maximal_ineq`）。
  2. `doob_maximal_ineq_real`（`ε : ℝ` 版，**核心**）：非负下鞅 `f`、`ε > 0` ⟹
     `P(max_{k≤n} f_k ≥ ε) ≤ E[f_n]/ε`。
     证明：`maximal_ineq` + 集合积分 ≤ 全积分（`setIntegral_le_integral`，用 `f ≥ 0`）
     + `ENNReal.toReal_mul` / `ENNReal.toReal_ofReal` 实数化。
  3. `doob_maximal_azuma_max`（**鞅版 Azuma 的极大形式**）：
     若指数过程 `k ↦ exp(λ·S_k)` 是下鞅（由条件 MGF 界经
     `submartingale_of_condexp_sub_nonneg` 得到，本文件以显式假设引入），则
     `P(max_{k≤n} S_k ≥ ε) ≤ exp(−λε)·E[exp(λ S_n)]`。
     证明：`{max S ≥ ε} ⊆ {exp(λε) ≤ max exp(λS_k)}`（`Finset.le_sup'_iff` + `exp` 单调），
     对非负下鞅 `k ↦ exp(λS_k)` 用 `doob_maximal_ineq_real`（取 `ε' = exp(λε)`），
     再用 `∫ ≤ exp(λε)·∫` 与 `exp(−λε) = 1/exp(λε)` 收尾。
  4. `condexp_exp_submartingale`：由条件 MGF 界（`condexp (𝒢 i) μ (exp(λ S_j)) ≤ exp(λ S_i)`）
     推出下鞅性（mathlib `submartingale_of_condexp_sub_nonneg`），
     从而把 3 的显式假设**消去**。

**诚实边界（标注）**：
- 3、4 中的「条件 MGF 界」是**外部输入**：一般测度论下
  `E[e^{λD}|F] ≤ e^{λ²c²/2}`（条件 Hoeffding 引理）本文件未证；
  有限计数版见 `RealAzumaMartingale.condExpFiber_hoeffding` / `RealHoeffdingMeasure`，
  测度论版见 `RealHoeffdingLemmaMeasure`。
- 极大值用 `Finset.sup' (Finset.range (n+1))`（离散有限时间）。
- 未做：Doob 的 `L^p` 不等式（`p > 1`）；连续时间极大不等式。
- 未做（诚实降级）：步骤 3 的原计划末尾「乘上 `exp(−λε)` 后与 `∫` 合并」被替换为
  更直接的 `∫ ≤ exp(λε)·∫` 路线；两者等价，但前者需要把常数因子从积分中提出来，
  本文件未走该路线。`E[exp(λS_n)] ≤ exp(λ²σ²/2)` 的 MGF 输入与 `λ = ε/σ²` 的
  参数代入**未做**（属外部引理，见上）。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open MeasureTheory
open scoped BigOperators NNReal ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}

/-! ## 一、Doob 极大不等式 -/

/-- **Doob 极大不等式（`ℝ≥0` 版）**：非负下鞅 `f`、`ε : ℝ≥0`，
`ε • μ{ε ≤ max_{k≤n} f_k} ≤ ∫_{ε ≤ max} f_n dμ`
（mathlib `MeasureTheory.maximal_ineq` 的命名包装）。 -/
theorem doob_maximal_ineq (f : ℕ → Ω → ℝ) (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    [IsFiniteMeasure μ] (ε : ℝ≥0) (n : ℕ) :
    ε • μ {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => f k ω)}
      ≤ ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => f k ω)}, f n ω ∂μ) := by
  have h := MeasureTheory.maximal_ineq (μ := μ) (𝒢 := 𝒢) (f := f) hsub hnonneg (ε := ε) n
  simpa using h

/-- **Doob 极大不等式（实值形式，核心）**：非负下鞅 `f`、`ε > 0`
⟹ `P(max_{k≤n} f_k ≥ ε) ≤ E[f_n]/ε`。 -/
theorem doob_maximal_ineq_real (f : ℕ → Ω → ℝ) (hsub : Submartingale f 𝒢 μ)
    (hnonneg : 0 ≤ f) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (μ {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => f k ω)}).toReal ≤ (∫ ω, f n ω ∂μ) / ε := by
  have hmain := doob_maximal_ineq (μ := μ) (𝒢 := 𝒢) f hsub hnonneg (ε := ε.toNNReal) n
  have hcoe : ((ε.toNNReal : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal ε hε.le
  simp only [hcoe] at hmain
  have hsub_int : (∫ ω in {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => f k ω)}, f n ω ∂μ) ≤ ∫ ω, f n ω ∂μ :=
    setIntegral_le_integral (hsub.integrable n) (Filter.Eventually.of_forall (hnonneg n))
  have hle : (ε.toNNReal : ℝ≥0∞) * μ {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => f k ω)}
      ≤ ENNReal.ofReal (∫ ω, f n ω ∂μ) :=
    le_trans hmain (ENNReal.ofReal_le_ofReal hsub_int)
  have hne_top : (ε.toNNReal : ℝ≥0∞) * μ {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => f k ω)} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hof : ENNReal.ofReal (∫ ω, f n ω ∂μ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hne_top hof).mpr hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg (hnonneg n))] at hreal
  have hcoe2 : ((ε.toNNReal : ℝ≥0) : ℝ≥0∞).toReal = ε := by
    rw [ENNReal.coe_toReal, hcoe]
  rw [hcoe2] at hreal
  rw [le_div_iff₀ hε]
  linarith [hreal]

/-! ## 二、鞅版 Azuma 的极大不等式 -/

/-- **指数极大尾界（核心）**：若 `k ↦ exp(λ S_k)` 是下鞅、`λ > 0`、`ε > 0`，则
`P(max_{k≤n} S_k ≥ ε) ≤ exp(−λε)·E[exp(λ S_n)]`。
证明：`{max S ≥ ε} ⊆ {exp(λε) ≤ max exp(λS_k)}`（`Finset.le_sup'_iff` + `exp` 单调），
再对非负下鞅 `k ↦ exp(λ S_k)` 用 `doob_maximal_ineq_real`（取 `ε' = exp(λε)`），
最后用 `∫_B ≤ ∫`（`setIntegral_le_integral`）把集合积分放大为全积分。 -/
theorem doob_maximal_azuma_max (S : ℕ → Ω → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hsub : Submartingale (fun k ω => Real.exp (lam * S k ω)) 𝒢 μ)
    [IsFiniteMeasure μ] {ε : ℝ} (_hε : 0 < ε) (n : ℕ) :
    (μ {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => S k ω)}).toReal
      ≤ Real.exp (-(lam * ε)) * (∫ ω, Real.exp (lam * S n ω) ∂μ) := by
  set A := {ω | ε ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => S k ω)} with hA
  set B := {ω | Real.exp (lam * ε) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => Real.exp (lam * S k ω))} with hB
  have hAB : A ⊆ B := by
    intro ω hω
    simp only [hA, hB, Set.mem_setOf_eq] at hω ⊢
    rw [Finset.le_sup'_iff] at hω ⊢
    obtain ⟨k, hk, hkle⟩ := hω
    exact ⟨k, hk, Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkle hlam.le)⟩
  have hmeasure : μ A ≤ μ B := measure_mono hAB
  have hnonneg : (0 : ℕ → Ω → ℝ) ≤ fun k ω => Real.exp (lam * S k ω) :=
    fun k ω => Real.exp_nonneg _
  have hexp : 0 < Real.exp (lam * ε) := Real.exp_pos _
  -- `doob_maximal_ineq_real` 作用在 `B` 上：`P(B) ≤ E[e^{λS_n}]/e^{λε}`
  have hdoob_raw : (μ B).toReal
      ≤ (∫ ω, Real.exp (lam * S n ω) ∂μ) / Real.exp (lam * ε) := by
    have hBμ : (μ B) = μ {ω | Real.exp (lam * ε) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_succ (fun k => Real.exp (lam * S k ω))} := by rw [hB]
    rw [hBμ]
    exact doob_maximal_ineq_real (μ := μ) (𝒢 := 𝒢)
      (f := fun k ω => Real.exp (lam * S k ω)) hsub hnonneg hexp n
  -- `A ⊆ B` ⟹ `P(A) ≤ P(B)`
  have hmB : (μ A).toReal ≤ (∫ ω, Real.exp (lam * S n ω) ∂μ) / Real.exp (lam * ε) :=
    le_trans (ENNReal.toReal_mono (measure_ne_top _ _) hmeasure) hdoob_raw
  have hstep : (∫ ω, Real.exp (lam * S n ω) ∂μ) / Real.exp (lam * ε)
      = Real.exp (-(lam * ε)) * (∫ ω, Real.exp (lam * S n ω) ∂μ) := by
    rw [div_eq_inv_mul, ← Real.exp_neg]
  calc (μ A).toReal
      ≤ (∫ ω, Real.exp (lam * S n ω) ∂μ) / Real.exp (lam * ε) := hmB
    _ = Real.exp (-(lam * ε)) * (∫ ω, Real.exp (lam * S n ω) ∂μ) := hstep

/-! ## 三、由条件 MGF 界得到指数下鞅性 -/

/-- **条件 MGF 界 ⟹ 指数过程是下鞅**：若对 `i ≤ j` 有
`exp(λ S_i) ≤ μ[exp(λ S_j) | 𝒢 i]`（a.e.），则 `k ↦ exp(λ S_k)` 是 `𝒢`-下鞅。
这是 `doob_maximal_azuma_max` 中 `hsub` 假设的**来源**，用 mathlib
`submartingale_of_condexp_sub_nonneg` 消去该假设：条件期望线性
（`condexp_sub`）把 `μ[exp(λS_j) − exp(λS_i) | 𝒢 i]` 化为
`μ[exp(λS_j)|𝒢 i] − μ[exp(λS_i)|𝒢 i]`，再由 `hmgf` 与「条件期望保持已可测函数」
（`condexp_of_stronglyMeasurable`）得非负。
（条件 MGF 界本身——条件 Hoeffding 引理——是外部输入，本文件**未证**，见文件头标注。）

**诚实边界（标注）**：这里使用的是「下鞅」方向的条件矩界
（`exp(λ S_i) ≤ E[exp(λ S_j)|𝒢 i]`），而不是更常见的上鞅型
`E[e^{λD}|F] ≤ e^{λ²c²/2}`；后者需先由鞅差结构构造指数鞅，本文件**未做**。 -/
theorem condexp_exp_submartingale (S : ℕ → Ω → ℝ) {lam : ℝ} [IsFiniteMeasure μ]
    (hadp : Adapted 𝒢 fun k ω => Real.exp (lam * S k ω))
    (hint : ∀ k, Integrable (fun ω => Real.exp (lam * S k ω)) μ)
    (hmgf : ∀ i j, i ≤ j → (fun ω => Real.exp (lam * S i ω))
      ≤ᵐ[μ] μ[fun ω => Real.exp (lam * S j ω) | 𝒢 i]) :
    Submartingale (fun k ω => Real.exp (lam * S k ω)) 𝒢 μ := by
  refine submartingale_of_condexp_sub_nonneg (μ := μ) (ℱ := 𝒢) hadp hint ?_
  intro i j hij
  have hlin : μ[(fun ω => Real.exp (lam * S j ω)) - (fun ω => Real.exp (lam * S i ω)) | 𝒢 i]
      =ᵐ[μ] μ[fun ω => Real.exp (lam * S j ω) | 𝒢 i] - μ[fun ω => Real.exp (lam * S i ω) | 𝒢 i] :=
    condexp_sub (hint j) (hint i)
  have hself : μ[fun ω => Real.exp (lam * S i ω) | 𝒢 i] = fun ω => Real.exp (lam * S i ω) :=
    condexp_of_stronglyMeasurable (𝒢.le i) (hadp i) (hint i)
  -- 逐点：条件矩界 ⟹ 0 ≤ E[e^{λS_j}|𝒢 i] − e^{λS_i}
  have hnonneg_ae : (0 : Ω → ℝ) ≤ᵐ[μ] μ[fun ω => Real.exp (lam * S j ω) | 𝒢 i]
      - μ[fun ω => Real.exp (lam * S i ω) | 𝒢 i] := by
    filter_upwards [hmgf i j hij] with ω hω
    have hselfω : (μ[fun ω => Real.exp (lam * S i ω) | 𝒢 i]) ω = Real.exp (lam * S i ω) := by
      rw [hself]
    show (0 : ℝ) ≤ (μ[fun ω => Real.exp (lam * S j ω) | 𝒢 i]) ω
      - (μ[fun ω => Real.exp (lam * S i ω) | 𝒢 i]) ω
    rw [hselfω]
    linarith [hω]
  -- 条件期望线性：把目标的条件期望化成上式之差
  have hgoal : (0 : Ω → ℝ) ≤ᵐ[μ] μ[(fun ω => Real.exp (lam * S j ω))
      - (fun ω => Real.exp (lam * S i ω)) | 𝒢 i] := by
    filter_upwards [hnonneg_ae, hlin] with ω h1 h2
    rw [h2]
    exact h1
  exact hgoal

end Lattice
