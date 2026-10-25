import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealHoeffdingLemmaMeasure
import Lattice.Lib.Concentration.RealUnionBound
/-!
# LATTICE: 有限候选集上的超参数选择泛化界 —— 并集界 + Hoeffding

方向（§5 验证行「模型选择 / 超参数选择」）：训练时要在一族 **k 个候选假设**
`Z : Fin k → α → ℝ`（或超参数配置）中按经验风险挑选一个；「挑选」本身引入
**选择偏差**（winner's curse）——单纯看被选中者的经验风险会系统性乐观。
本文件把 `RealHoeffding` 的单假设指数型集中界与 `RealUnionBound` 的并集界
组合，给出**同时**对所有候选成立的均匀偏差界，并由此得到选择偏差的显式上界。

**样本空间**：`Fin m → α`（= 从有限总体 α 均匀抽取 m 个样本，即独立重复），
均匀测度 `uniformProb`（`RealSamplingBoost`）；第 4 节另在任意有限空间 Ω 上
证明一般的「尾积分 / 截断期望」引理。

**主结果**：
1. `single_dev_tail`：固定假设 h 的双边偏差尾界
   `μ{|empRisk_h − risk_h| ≥ t} ≤ 2·e^{−m t²/8}`（单假设 Hoeffding）。
2. `all_deviations_tail`（核心，并集界）：同时对所有 k 个候选，
   `μ{∃h, |empRisk_h − risk_h| ≥ t} ≤ k·(2·e^{−m t²/8})`。
3. `hyperparameter_selection_bound`（核心，good 事件上的确定性选择界）：
   若样本落在 good 事件（所有候选偏差 ≤ t），且 hhat 是经验风险最小者、
   h* 是真实风险最小者，则 `risk(hhat) − risk(h*) ≤ 2t`。
4. `hyperparameter_selection_bound_prob`（核心，概率化）：
   上述 good 事件概率 ≥ `1 − k·(2·e^{−m t²/8})`。
5. `selection_bias_expectation`（核心，选择偏差的期望上界）：
   ERM 选择子 hhat(w) 的期望超额风险
   `E[risk(hhat) − risk(h*)] ≤ 2t + 2·(k·(2·e^{−m t²/8}))`。
6. `uniformExpectation_le_eps_add_max_mul_prob`：一般的「好事件以外 ≤ ε、
   全体 ≤ M」⟹ `E X ≤ ε + M·μ(bad)` 截断期望引理。

**诚实边界（全部显式标注）**：
· 概率空间是**有限计数**（均匀 / 等概率）空间，非一般测度；期望 = 计数平均。
· 损失有界：`∀ h x, |Z h x| ≤ 1`；因此真实风险 ∈ [−1,1]，风险差 ≤ 2。
· **常数诚实**：本项目 Hoeffding 尾指数为 `e^{−m t²/8}`（见 `RealHoeffding`
  的诚实标注：完整 Hoeffding 引理给 `e^{−m t²/2}`，此处因保守常数 8）。
  于是反解 t 时得到 `t = sqrt(8·log(2k/δ)/m)` 型半径，而**不是**文献经典的
  `sqrt(log|H|/(2m))` 型常数——差异纯粹来自本项目 Hoeffding 的常数 8
  （若用 `e^{−m t²/2}` 则得 `sqrt(2 log(2k/δ)/m)`）。已知情标注，未证经典常数。
· `hmin`（hhat 经验最优）是 ERM / best-in-class 的**显式假设**，不构造训练过程；
  本文件只做「给定 ERM 性质 ⟹ 泛化界」。
  **历史沿革（已否证 / 已删除）**：`hminRisk`（h* 真实最优）曾与 `hmin` 并列为显式假设，
  但证明体逐行只用 `hmin` 与 `hgood`，Lean 实测 `unused variable 'hminRisk'` ⟹ 该假设
  装饰性，已删除，见 `hyperparameter_selection_bound` 的 docstring 与
  `selection_bias_expectation` 的 docstring；两处均已删除，命题严格更一般。
· ERM 选择子 `ermSelector` 用有限集最小元 `Finset.exists_min_image` 构造
  （非可计算选择），仅在 k > 0（候选集非空）时有定义。
· 不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 经验风险、真实风险与偏差事件 -/

/-- 假设 `h` 在样本 `w : Fin m → α` 上的**经验风险**（m 个样本上损失的平均）。 -/
def hypEmpRisk {α : Type*} {k : ℕ} (Z : Fin k → α → ℝ) (m : ℕ) (w : Fin m → α)
    (h : Fin k) : ℝ :=
  (∑ i : Fin m, Z h (w i)) / (m : ℝ)

/-- 假设 `h` 的**真实风险**（总体 α 上的均匀期望损失）。 -/
def hypRisk {α : Type*} [Fintype α] {k : ℕ} (Z : Fin k → α → ℝ) (h : Fin k) : ℝ :=
  uniformExpectation (Z h)

/-- **偏差事件**：存在某个候选 `h`，其经验风险与真实风险之差 ≥ t（绝对值）。
这是「至少一个候选被数据误导」的坏事件。 -/
def devEvent {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (Z : Fin k → α → ℝ) (m : ℕ)
    (t : ℝ) : Finset (Fin m → α) :=
  Finset.univ.filter (fun w => ∃ h : Fin k, t ≤ |hypEmpRisk Z m w h - hypRisk Z h|)

/-- 固定假设 `h` 的**单点偏差事件**：`|empRisk_h − risk_h| ≥ t`。 -/
def singleDevEvent {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (Z : Fin k → α → ℝ)
    (m : ℕ) (t : ℝ) (h : Fin k) : Finset (Fin m → α) :=
  Finset.univ.filter (fun w => t ≤ |hypEmpRisk Z m w h - hypRisk Z h|)

/-! ## 单假设尾界（Hoeffding，直接引用 RealHoeffding） -/

/-- 固定假设的单点双边尾界：`μ{ |empRisk_h − risk_h| ≥ t } ≤ 2·e^{−m t²/8}`。
直接由 `hoeffding_two_sided` 实例化：`X := Z h`、`μ := uniformExpectation (Z h)`
（`hmean := rfl`）、界 `|Z h x| ≤ 1`。 -/
theorem single_dev_tail {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (Z : Fin k → α → ℝ)
    (m : ℕ) (t : ℝ) (hm : 0 < m) (hN : 0 < Fintype.card α)
    (hb : ∀ h x, |Z h x| ≤ 1) (ht : 0 < t) (h : Fin k) :
    uniformProb (singleDevEvent Z m t h) ≤ 2 * Real.exp (-(m : ℝ) * t ^ 2 / 8) := by
  simpa [singleDevEvent, hypEmpRisk, hypRisk] using
    hoeffding_two_sided (uniformExpectation (Z h)) m hm hN rfl (hb h) ht

/-! ## 主结果一：并集界 —— 对所有候选同时成立的均匀偏差界 -/

/-- **主结果（并集界 + Hoeffding）**：对 k 个候选的**联合**坏事件，
`μ{∃h, |empRisk_h − risk_h| ≥ t} ≤ k·(2·e^{−m t²/8})`。
证明路线：`devEvent ⊆ ⋃_h singleDevEvent_h`（逐点取见证 h）+ `uniformProb`
单调 + 并集界 `union_prob_le_sum` + 单点尾界 + `Finset.sum_const`。 -/
theorem all_deviations_tail {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (Z : Fin k → α → ℝ)
    (m : ℕ) (t : ℝ) (hm : 0 < m) (hN : 0 < Fintype.card α) (hb : ∀ h x, |Z h x| ≤ 1)
    (ht : 0 < t) :
    uniformProb (devEvent Z m t) ≤ (k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8)) := by
  -- 子集：devEvent ⊆ ⋃_{h} singleDevEvent h
  have hsub : devEvent Z m t ⊆
      Finset.univ.biUnion (fun h : Fin k => singleDevEvent Z m t h) := by
    intro w hw
    rw [devEvent, Finset.mem_filter] at hw
    obtain ⟨-, hwit⟩ := hw
    rcases hwit with ⟨h, hh⟩
    refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, ?_⟩
    rw [singleDevEvent, Finset.mem_filter]
    exact ⟨Finset.mem_univ w, hh⟩
  -- 单调性 + 并集界 + 单点尾界 + 常数和
  calc
    uniformProb (devEvent Z m t)
        ≤ uniformProb (Finset.univ.biUnion (fun h : Fin k => singleDevEvent Z m t h)) := by
          unfold uniformProb
          exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
            (Nat.cast_nonneg _)
    _ ≤ ∑ h : Fin k, uniformProb (singleDevEvent Z m t h) :=
          union_prob_le_sum (Finset.univ : Finset (Fin k)) (fun h => singleDevEvent Z m t h)
    _ ≤ ∑ _h : Fin k, (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8)) :=
          Finset.sum_le_sum (fun h _ => single_dev_tail Z m t hm hN hb ht h)
    _ = (k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 主结果二：good 事件上的确定性选择界 -/

/-- **主结果（确定性选择界）**：若样本 `w` 满足所有候选的偏差 ≤ t（good 事件），
`hhat` 是经验风险最小者、`h*` 是真实风险最小者，则超额风险
`risk(hhat) − risk(h*) ≤ 2t`。
证明：`risk(hhat) ≤ empRisk(hhat) + t ≤ empRisk(h*) + t ≤ risk(h*) + 2t`
（两侧 `abs_le.mp` + 经验最优性 `hmin`）；`linarith`。

**Q3B2 更正（删除 `hminRisk`，Lean 实测 `unused variable 'hminRisk'`，原 135:5）**：
原陈述带 `hminRisk : ∀ h, hypRisk Z hstar ≤ hypRisk Z h`（`h*` 是**真实**风险最小者），
但证明体**逐行只用** `hmin`（**经验**风险最优性）与 `hgood`（两侧 `abs_le.mp`），
**完全不用** `hminRisk`。⟹ 该假设是**装饰性的**：
它让人以为「`h*` 必须是真实最优」，而定理对**任意** `hstar` 都成立
（只要 `hgood` 对 `hstar` 成立）。已**删除**，命题**严格更一般**。
注意 调用方 `hyperparameter_selection_bound_prob` / `selection_bias_expectation`
已同步更新（它们此前按位置传入 `hminRisk`）。
**注**：`selection_bias_expectation` / `selection_bias_expectation_delta`
的 `hminRisk` **亦已删除**——它在 `selection_bias_expectation` 中唯一的用途是
喂给当时尚存的 `h0`（非负性）前提；本轮删除 `h0` 后它即成死前提
（复探针实测 `unused variable 'hminRisk'`）。两处均已删除，命题严格更一般。 -/
theorem hyperparameter_selection_bound {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (Z : Fin k → α → ℝ) (m : ℕ) (t : ℝ) (w : Fin m → α) (hhat hstar : Fin k)
    (hmin : ∀ h, hypEmpRisk Z m w hhat ≤ hypEmpRisk Z m w h)
    (hgood : ∀ h, |hypEmpRisk Z m w h - hypRisk Z h| ≤ t) :
    hypRisk Z hhat - hypRisk Z hstar ≤ 2 * t := by
  have h1 : hypRisk Z hhat ≤ hypEmpRisk Z m w hhat + t := by
    have := (abs_le.mp (hgood hhat)).1
    linarith
  have h2 : hypEmpRisk Z m w hhat ≤ hypEmpRisk Z m w hstar := hmin hstar
  have h3 : hypEmpRisk Z m w hstar ≤ hypRisk Z hstar + t := by
    have := (abs_le.mp (hgood hstar)).2
    linarith
  linarith

/-! ## 主结果三：概率化选择界 -/

/-- **主结果（概率化选择界）**：`devEvent` 的并集界（第一合取项），且存在一个
good 事件 `good ⊆ univ`（取 `univ \ devEvent`），其概率 ≥ `1 − k·(2·e^{−m t²/8})`，
且其上对任意经验最优 `hhat` 与真实最优 `h*` 都有超额风险 ≤ 2t。 -/
theorem hyperparameter_selection_bound_prob {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (Z : Fin k → α → ℝ) (m : ℕ) (t : ℝ) (hm : 0 < m) (hN : 0 < Fintype.card α)
    (hb : ∀ h x, |Z h x| ≤ 1) (ht : 0 < t) :
    uniformProb (devEvent Z m t) ≤ (k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8)) ∧
      ∃ good : Finset (Fin m → α),
        1 - (k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8)) ≤ uniformProb good ∧
          ∀ w ∈ good, ∀ hhat hstar : Fin k,
            (∀ h, hypEmpRisk Z m w hhat ≤ hypEmpRisk Z m w h) →
            (∀ h, hypRisk Z hstar ≤ hypRisk Z h) →
            hypRisk Z hhat - hypRisk Z hstar ≤ 2 * t := by
  have htail := all_deviations_tail Z m t hm hN hb ht
  have hN' : 0 < Fintype.card (Fin m → α) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact pow_pos hN m
  have hsub : devEvent Z m t ⊆ (Finset.univ : Finset (Fin m → α)) := Finset.subset_univ _
  have hle' : (devEvent Z m t).card ≤ Fintype.card (Fin m → α) := Finset.card_le_univ _
  have hcompl : uniformProb ((Finset.univ : Finset (Fin m → α)) \ devEvent Z m t)
      = 1 - uniformProb (devEvent Z m t) := by
    unfold uniformProb
    rw [Finset.card_sdiff hsub, Finset.card_univ, Nat.cast_sub hle', sub_div,
      div_self (ne_of_gt (Nat.cast_pos.mpr hN'))]
  refine ⟨htail, Finset.univ \ devEvent Z m t, ?_, ?_⟩
  · rw [hcompl]
    exact sub_le_sub_left htail 1
  · intro w hw hhat hstar hmin hminRisk
    refine hyperparameter_selection_bound Z m t w hhat hstar hmin ?_
    intro h
    have hw' : w ∉ devEvent Z m t := (Finset.mem_sdiff.mp hw).2
    have hno : ¬ (∃ hh : Fin k, t ≤ |hypEmpRisk Z m w hh - hypRisk Z hh|) := by
      intro hp
      exact hw' (by rw [devEvent, Finset.mem_filter]; exact ⟨Finset.mem_univ w, hp⟩)
    exact le_of_lt (lt_of_not_ge (not_exists.mp hno h))

/-! ## 工具：指示函数的期望与截断期望（尾积分）引理 -/

/-- 指示函数的求和等于集合基数：`Σ_w [w ∈ s] = |s|`（实数嵌入）。 -/
theorem indicator_sum {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (s : Finset Ω) :
    (∑ w : Ω, (if w ∈ s then (1 : ℝ) else 0)) = (s.card : ℝ) := by
  have hfilter : Finset.univ.filter (fun w => w ∈ s) = s := by
    ext w
    simp
  rw [show (∑ w : Ω, (if w ∈ s then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun w => w ∈ s)).card : ℝ) by
        simpa using Finset.sum_boole (fun w => w ∈ s) (Finset.univ : Finset Ω)]
  rw [hfilter]

/-- 指示函数的均匀期望等于该集合的均匀概率：`E[1_s] = μ(s)`。 -/
theorem uniformExpectation_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (s : Finset Ω) :
    uniformExpectation (fun w => if w ∈ s then (1 : ℝ) else 0) = uniformProb s := by
  unfold uniformExpectation uniformProb
  rw [indicator_sum]

/-- **截断期望（尾积分）引理**：`X` 逐点 ≤ M、在坏集 `s` 之外 ≤ ε
（ε ≥ 0）⟹ `E X ≤ ε + M·μ(s)`。
证明路线：逐点 `X ≤ ε + M·1_s`（`w ∈ s` 时 `X ≤ M ≤ ε + M·1`；否则 `X ≤ ε`）
⟹ 取期望（求和单调 + 除以 |Ω|）⟹ `E[ε + M·1_s] = ε + M·E[1_s]`（线性 +
指示函数期望引理）。

**Q3B2 更正（删除 `hs`/`hM0`/`h0` 三个未使用假设，Lean 实测原 209:30 `'hs'`、
209:66 `'hM0'`、210:5 `'h0'`）**：
· `hs : s ⊆ Finset.univ` —— **恒真**（`Finset.subset_univ`），证明体从不引用它；
· `hM0 : 0 ≤ M` —— 证明体只在 `w ∈ s` 分支用 `hM w` 与 `hε` 经 `nlinarith`
  得 `X w ≤ ε + M`（**不需要** `M ≥ 0`，因为该分支不需要 `M·1 ≥ 0` 的下界）；
· `h0 : ∀ w, 0 ≤ X w` —— 证明体全程只用逐点不等式 `hpt` 与求和单调，
  **不需要** `X` 的非负性。
⟹ 三者皆是**装饰性前提**（读者会误以为缺一不可）。已**删除**，命题**严格更一般**。
注意 **未删 / 未改**：`ε ≥ 0`（`hε`）与 `M` 本身**保留** —— `hε` 在 `w ∈ s` 分支
经 `nlinarith` 参与（`X ≤ M ≤ ε + M`），且它是「界 `ε` 有意义」的语义前提。
`M ≥ 0` 虽在本证明中未用，但**结论** `ε + M·μ(s)` 要作为**上界**才有意义
（`M < 0` 时该式随 `μ(s)` 增大而**减小**，语义上不再是「好的上界」）；
故 `M` 作为形参保留，仅在 docstring 注明「本证明不需要 `M ≥ 0`，但取上界时不变量应满足」。
**依据**：`PROCESS.md §4.6`（`unused variable` 是假设写松的最强机械信号）。 -/
theorem uniformExpectation_le_eps_add_max_mul_prob {Ω : Type*} [Fintype Ω] (X : Ω → ℝ)
    (ε M : ℝ) (s : Finset Ω) (hε : 0 ≤ ε)
    (hM : ∀ w, X w ≤ M) (hgood : ∀ w, w ∉ s → X w ≤ ε) :
    uniformExpectation X ≤ ε + M * uniformProb s := by
  classical
  by_cases hN : Fintype.card Ω = 0
  · have hNr : (Fintype.card Ω : ℝ) = 0 := by rw [hN]; norm_num
    have hX : uniformExpectation X = 0 := by
      unfold uniformExpectation
      rw [hNr]
      norm_num
    have hPs : uniformProb s = 0 := by
      unfold uniformProb
      rw [hNr]
      norm_num
    rw [hX, hPs, mul_zero, add_zero]
    linarith
  · have hNr : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hN
    have hpt : ∀ w, X w ≤ ε + M * (if w ∈ s then (1 : ℝ) else 0) := by
      intro w
      by_cases hw : w ∈ s
      · rw [if_pos hw]
        have := hM w
        nlinarith
      · rw [if_neg hw, mul_zero, add_zero]
        exact hgood w hw
    have hA : (∑ _w : Ω, ε) / (Fintype.card Ω : ℝ) = ε := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ ε hNr
    have hB : (∑ w : Ω, M * (if w ∈ s then (1 : ℝ) else 0)) / (Fintype.card Ω : ℝ)
        = M * uniformProb s := by
      unfold uniformProb
      rw [← Finset.mul_sum, indicator_sum, mul_div_assoc]
    calc
      uniformExpectation X
          ≤ uniformExpectation (fun w => ε + M * (if w ∈ s then (1 : ℝ) else 0)) := by
            unfold uniformExpectation
            exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun w _ => hpt w))
              (Nat.cast_nonneg _)
      _ = ε + M * uniformProb s := by
            unfold uniformExpectation
            rw [Finset.sum_add_distrib, add_div, hA, hB]

/-! ## 主结果四：ERM 选择子与选择偏差的期望上界 -/

/-- **ERM 选择子**（构造）：在候选集 `Fin k` 上取经验风险最小者。
用 `Finset.exists_min_image` 在非空有限集 `univ` 上取最小元；`hk : 0 < k`
保证候选集非空（提供见证 `⟨0, hk⟩`）。诚实标注：这是非可计算选择。 -/
noncomputable def ermSelector {α : Type*} [Fintype α] {k : ℕ} (Z : Fin k → α → ℝ) (m : ℕ)
    (w : Fin m → α) (hk : 0 < k) : Fin k :=
  (Finset.exists_min_image (Finset.univ : Finset (Fin k)) (fun h => hypEmpRisk Z m w h)
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩).choose

/-- **ERM 选择子的最优性**：`ermSelector` 的经验风险 ≤ 任意候选的经验风险。 -/
theorem ermSelector_spec {α : Type*} [Fintype α] {k : ℕ} (Z : Fin k → α → ℝ) (m : ℕ)
    (w : Fin m → α) (hk : 0 < k) :
    ∀ h, hypEmpRisk Z m w (ermSelector Z m w hk) ≤ hypEmpRisk Z m w h := by
  have hspec := (Finset.exists_min_image (Finset.univ : Finset (Fin k))
    (fun h => hypEmpRisk Z m w h) ⟨⟨0, hk⟩, Finset.mem_univ _⟩).choose_spec
  intro h
  simpa only [ermSelector] using hspec.2 h (Finset.mem_univ h)

/-- 真实风险的绝对值 ≤ 1（`|Z h x| ≤ 1` 时；由 `abs_mean_le_one` 得出）。 -/
theorem abs_hypRisk_le_one {α : Type*} [Fintype α] {k : ℕ} (Z : Fin k → α → ℝ)
    (hN : 0 < Fintype.card α) (hb : ∀ h x, |Z h x| ≤ 1) (h : Fin k) :
    |hypRisk Z h| ≤ 1 := by
  unfold hypRisk
  exact abs_mean_le_one (uniformExpectation (Z h)) hN rfl (hb h)

/-- **主结果（选择偏差的期望上界）**：ERM 选择子 `hhat(w) = ermSelector` 的期望超额
风险（相对真实最优 `h*`）满足
`E[risk(hhat) − risk(h*)] ≤ 2t + 2·(k·(2·e^{−m t²/8}))`。
证明：令 `X w := risk(hhat(w)) − risk(h*)`。`X ≤ 2`
（两侧风险 ∈ [−1,1]）、在 `devEvent` 之外 `X ≤ 2t`（`hyperparameter_selection_bound`），
代入截断期望引理（ε = 2t、M = 2、s = devEvent）并对 `μ(devEvent)` 用并集界。

**Q3B2 更正（删除 `hminRisk`，Lean 实测 `unused variable 'hminRisk'`，原 312:5）**：
本轮同时删除了 `uniformExpectation_le_eps_add_max_mul_prob` 的 `h0`（非负性）前提，
而 `hminRisk` 在本定理中**唯一**的用途正是喂给那个 `h0`
（`have h0 : ∀ w, 0 ≤ … := fun w => sub_nonneg.mpr (hminRisk …)`）。
`h0` 一经删除，`hminRisk` 即为**死前提**（Lean 复探针实测报告 unused）。
⟹ 已**删除**，命题**严格更一般**：本界对**任意** `hstar` 成立，
不再要求 `h*` 是真实风险最优。 -/
theorem selection_bias_expectation {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (Z : Fin k → α → ℝ) (m : ℕ) (t : ℝ) (hk : 0 < k) (hm : 0 < m)
    (hN : 0 < Fintype.card α) (hb : ∀ h x, |Z h x| ≤ 1) (ht : 0 < t) (hstar : Fin k) :
    uniformExpectation (fun w => hypRisk Z (ermSelector Z m w hk) - hypRisk Z hstar)
      ≤ 2 * t + 2 * ((k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8))) := by
  have hM : ∀ w, hypRisk Z (ermSelector Z m w hk) - hypRisk Z hstar ≤ 2 := by
    intro w
    have h1 := (abs_le.mp (abs_hypRisk_le_one Z hN hb (ermSelector Z m w hk))).2
    have h2 := (abs_le.mp (abs_hypRisk_le_one Z hN hb hstar)).1
    linarith
  have hgood : ∀ w, w ∉ devEvent Z m t →
      hypRisk Z (ermSelector Z m w hk) - hypRisk Z hstar ≤ 2 * t := by
    intro w hw
    have hgood' : ∀ h, |hypEmpRisk Z m w h - hypRisk Z h| ≤ t := by
      intro h
      have hno : ¬ (∃ hh : Fin k, t ≤ |hypEmpRisk Z m w hh - hypRisk Z hh|) := by
        intro hp
        exact hw (by rw [devEvent, Finset.mem_filter]; exact ⟨Finset.mem_univ w, hp⟩)
      exact le_of_lt (lt_of_not_ge (not_exists.mp hno h))
    exact hyperparameter_selection_bound Z m t w (ermSelector Z m w hk) hstar
      (ermSelector_spec Z m w hk) hgood'
  calc
    uniformExpectation (fun w => hypRisk Z (ermSelector Z m w hk) - hypRisk Z hstar)
        ≤ 2 * t + 2 * uniformProb (devEvent Z m t) :=
          uniformExpectation_le_eps_add_max_mul_prob _ (2 * t) 2 (devEvent Z m t)
            (by linarith) hM hgood
    _ ≤ 2 * t + 2 * ((k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8))) := by
          have hbnd := all_deviations_tail Z m t hm hN hb ht
          linarith

/-! ## 主结果五：显式半径 δ-形式（诚实常数） -/

/-- **主结果（δ 形式的期望选择偏差界）**：取显式半径
`t = sqrt(8·log(2k/δ)/m)`，则并集界项满足 `k·(2·e^{−m t²/8}) ≤ δ`，
从而期望超额风险 `≤ 2·sqrt(8·log(2k/δ)/m) + 2δ`。
**诚实标注**：这是本项目 Hoeffding 常数（指数 `e^{−m t²/8}`）下的半径；
经典文献（指数 `e^{−m t²/2}`）对应 `t = sqrt(2·log(2k/δ)/m)`。假设
`0 < δ`、`δ < 2k`（保证 `log(2k/δ) > 0`，半径为正）。 -/
theorem selection_bias_expectation_delta {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (Z : Fin k → α → ℝ) (m : ℕ) (δ : ℝ) (hk : 0 < k) (hm : 0 < m)
    (hN : 0 < Fintype.card α) (hb : ∀ h x, |Z h x| ≤ 1) (hδ : 0 < δ)
    (hδk : δ < 2 * (k : ℝ)) (hstar : Fin k) :
    uniformExpectation (fun w => hypRisk Z (ermSelector Z m w hk) - hypRisk Z hstar)
      ≤ 2 * Real.sqrt (8 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) + 2 * δ := by
  set t : ℝ := Real.sqrt (8 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) with ht_def
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h2k : 0 < 2 * (k : ℝ) := by linarith
  have hq : 0 < 2 * (k : ℝ) / δ := div_pos h2k hδ
  have h1lt : 1 < 2 * (k : ℝ) / δ := (one_lt_div hδ).mpr hδk
  have hlog : 0 < Real.log (2 * (k : ℝ) / δ) := Real.log_pos h1lt
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hrad : 0 < 8 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ) :=
    div_pos (mul_pos (by norm_num) hlog) hmR
  have htpos : 0 < t := Real.sqrt_pos_of_pos hrad
  have hsq : t ^ 2 = 8 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ) := Real.sq_sqrt hrad.le
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  -- 指数项化为 δ/(2k)
  have hstep : (m : ℝ) * t ^ 2 / 8 = Real.log (2 * (k : ℝ) / δ) := by
    rw [hsq, ← mul_div_assoc,
      mul_div_cancel_left₀ (8 * Real.log (2 * (k : ℝ) / δ)) hmne]
    ring
  have harg : -(m : ℝ) * t ^ 2 / 8 = -Real.log (2 * (k : ℝ) / δ) := by
    rw [show -(m : ℝ) * t ^ 2 / 8 = -((m : ℝ) * t ^ 2 / 8) by ring, hstep]
  have hexp : 2 * Real.exp (-(m : ℝ) * t ^ 2 / 8) = δ / (k : ℝ) := by
    rw [harg, Real.exp_neg, Real.exp_log hq, inv_div]
    rw [show δ / (2 * (k : ℝ)) = (δ / (k : ℝ)) / 2 by rw [div_div, mul_comm]]
    exact mul_div_cancel₀ (δ / (k : ℝ)) (by norm_num : (2 : ℝ) ≠ 0)
  have htail : (k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8)) ≤ δ := by
    rw [hexp, ← mul_div_assoc, mul_div_cancel_left₀ δ (ne_of_gt hkR)]
  have hbias := selection_bias_expectation Z m t hk hm hN hb htpos hstar
  calc
    uniformExpectation (fun w => hypRisk Z (ermSelector Z m w hk) - hypRisk Z hstar)
        ≤ 2 * t + 2 * ((k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / 8))) := hbias
    _ ≤ 2 * t + 2 * δ := by linarith
    _ = 2 * Real.sqrt (8 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) + 2 * δ := by rw [ht_def]

/-! ## 注：闭环语义（超参数选择的泛化保证如何接入验证线）
    1. `single_dev_tail` 给出单候选的指数尾界
       （**注意 R3 更正（悬空引用）**：该引理**不在** `RealHoeffding`，
       而在**本文件同 module** 内——`RealHyperparameterBound.lean:83`。
       全库为扁平 `namespace Lattice`，故正确引用是**裸名**
       `single_dev_tail`，**不是** `RealHoeffding.single_dev_tail`）；
    2. 本文件 `all_deviations_tail` 用 `RealUnionBound.union_prob_le_sum`
       把 k 个候选的尾界叠加为「同时成立」的均匀偏差界 k·2e^{−mt²/8}；
    3. `hyperparameter_selection_bound` 在 good 事件上把均匀偏差转化为
       **选择偏差** `risk(hhat) − risk(h*) ≤ 2t`（ERM 泛化界的经典 2t 形式）；
    4. `hyperparameter_selection_bound_prob` / `selection_bias_expectation`
       把它概率化 / 期望化，得到可复用的模型选择保证；
    5. `uniformExpectation_le_eps_add_max_mul_prob` 是通用的尾积分工具，
       可复用于其它「好事件概率 + 界」型的期望估计。

    诚实的常数差异（见文件头）：本项目 Hoeffding 指数为 e^{−mt²/8}，
    故 δ 形式半径为 sqrt(8 log(2k/δ)/m)，**不是**经典的
    sqrt(log|H|/(2m)) 型；这是本文件最重要的诚实标注。 -/

/-! ## 主结果六（B30）：**经典 Hoeffding 常数**（替换保守的 8）

前述结论的指数都是 `e^{−m t²/8}`，常数 `8` 来自 `RealHoeffding` 的保守处理
（`hoeffding_lemma_shifted` 只把 `|X − μ| ≤ 2` 当作界，丢掉了区间结构）。
本节用 **`RealHoeffdingLemmaMeasure.hoeffding_lemma_measure`**——即
**一般测度论 Hoeffding 引理** `mgf ≤ exp(t²R²/2)`（`R = max b (−a)`）——
在**同一有限计数概率空间**上重做整条链，把常数从 `8` 收紧到经典的 `2`。

**关键的正确性约束（CORRECTIONS B19，务必遵守）**：一般区间 `[a,b]` 上的
常数**不是** `exp(t²(b−a)²/8)`，而是 `exp(t²R²/2)`，`R = max b (−a)`；
`(b−a)²/8` 只在**关于 0 对称**的区间上成立。本节全程使用
`R = max b (−a)` 的**半径形式**（以参数 `c` 传入）。

**链条（本轮实际交付）**：
1. `chord_exp_le_cosh_sinh`：弦界（复用 `chord_hull_abs`，**只读**）；
2. `mgf_count_le_exp_half_sq`：**有限计数空间的 Hoeffding 引理**
   （`|X| ≤ c`、零均值 ⟹ `E[e^{λX}] ≤ e^{λ²c²/2}`，**任意半径 `c`**），
   由弦界 + `cosh_le_exp_half_sq` 直接得到（**不引入测度论**）；
3. `hoeffding_tail_classic_aux` / `hoeffding_tail_classic`：**经典常数尾界**
   `P(X̄ − μ ≥ t) ≤ e^{−m t²/(2c²)}` —— 常数 **2** 取代保守的 **8**；
4. `all_deviations_tail_classic`：**并集界**（双边化），常数 2；
5. `classic_delta_exponent`：δ 形式半径的**指数项**收紧
   （`k·(2·e^{−m t²/(2R²)}) ≤ δ`，即半径 `√(2 log(2k/δ)/m)·R`）。

注意 **可达性提示（v14，S9 重复实现审计发现；coordinator 已核实）**：
**本文件的经典常数（`/2`）比 `RealHoeffding` 的保守常数（`/8`）紧 4 倍，
但下游几乎全部用的是松版 —— 本文件的紧版目前"零下游"**。
- **弱版**：`RealHoeffding` 的 `hoeffding_tail`（写 `RealHoeffding.lean:423`；注意该文件的
  第 406 行是 `hoeffding_two_sided` 证明体内的 `have hA`，曾误引为此行）给出 **`exp(−n·t²/8)`**，
  其**直接 importer 计数 = 22**（口径：全库 `import RealHoeffding` 的文件数；实测这些
  importer 互不传递导入该模块，故按该口径直接 importer 数即 22，非 16）；
- **本文件的紧版**：`hoeffding_tail_classic_aux` / `hoeffding_tail_classic`
  —— **传递 importer = 0**；
- **下游把 `/8` 硬编码进 30 处陈述级位置**（`RealBanditTheory` 6、`RealEarlyStoppingStatistics` 4、
  `RealGeneralizationBound` 4、`RealDistillGeneralization` 2、`RealRademacher` 3、本文件 11）；
- 注意 **硬障碍**：`RealHyperparameterBound.lean:2` **import `RealHoeffding`** ⟹
  **把弱版改为复用紧版会成环**；必须先做**叶子模块下沉**（独立立项），
  **不是"改一个 import"就能解决**。
- ⇒ **本文件自身没有写错**（上面的"常数 2 取代保守的 8"是诚实的）；问题在于
  **两侧 docstring 各自诚实、合起来不诚实** —— 读者读本文件时看不到
  **全库 7 个模块仍在用松版**。**处置：仅加本交叉引用（零风险），下沉重构另立项。**

**未做（诚实标注，勿引用未声明的名字）**：
· `hoeffding_two_sided_classic`（独立命名的双边尾界）**未单独提供**——
  双边化已**内联在** `all_deviations_tail_classic` 的 `hsingle` 分支里；
· `selection_bias_expectation_classic` / `selection_bias_expectation_delta_classic`
  **未做**：把经典常数接到 §六的选择偏差链（`ermSelector` +
  `uniformExpectation_le_eps_add_max_mul_prob`）上是**机械重接**，
  但**本轮未实现**（**标注：未做**）；
· `classic_beats_conservative`（新旧常数严格更强性的显式定理）**未做**——
  该事实是显然的（`e^{−mt²/2} ≤ e^{−mt²/8}`，`t ≥ 0`），
  但**未写成定理**（**标注：未做**）。
-/

/-- **弦界（只读复用 `RealHoeffdingLemmaMeasure.chord_hull_abs`）**：
`|y| ≤ c`、`c > 0` ⟹ `e^{ty} ≤ cosh(tc) + (y/c)·sinh(tc)`（对**任意** `t` 成立）。
`y` 只以一次项出现，取期望后被零均值消去——这是拿到经典常数的关键。 -/
theorem chord_exp_le_cosh_sinh {y c t : ℝ} (hc : 0 < c) (hy : |y| ≤ c) :
    Real.exp (t * y) ≤ Real.cosh (t * c) + (y / c) * Real.sinh (t * c) :=
  chord_hull_abs hc hy

/-- **有限计数空间的 Hoeffding 引理（经典常数，核心）**：`α` 有限、`N = |α| > 0`、
`|X x| ≤ c`（`c > 0`）、`Σ_x X x = 0` ⟹
`E[e^{λX}] ≤ e^{λ²c²/2}`（**对任意 `λ : ℝ`**）。

证明：逐点弦界 `chord_hull_abs`（`|X x| ≤ c`）⟹ 取计数期望 ⟹
`sinh` 项被 `Σ X = 0` 消去 ⟹ `E ≤ cosh(λc)` ⟹
`Real.cosh_le_exp_half_sq` 收尾。

**与 `RealHoeffding.hoeffding_lemma` 的区别（B30 的要点）**：后者只对
`c = 1` 且用「`|X − μ| ≤ 2`」的粗界（得常数 `8`）；本定理对**任意半径 `c`**
给出 `λ²c²/2`，正是经典 Hoeffding 引理的形式，且**不依赖测度论**。 -/
theorem mgf_count_le_exp_half_sq {α : Type*} [Fintype α] {X : α → ℝ} {c lam : ℝ}
    (hN : 0 < Fintype.card α) (hc : 0 < c) (hb : ∀ x : α, |X x| ≤ c)
    (hzero : (∑ x : α, X x) = 0) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) := by
  -- 逐点弦界
  have hchord : ∀ x : α, Real.exp (lam * X x)
      ≤ Real.cosh (lam * c) + (X x / c) * Real.sinh (lam * c) :=
    fun x => chord_hull_abs hc (hb x)
  -- 取和：`Σ (cosh + (X/c)·sinh) = N·cosh`（零均值消去 `sinh` 项）
  have hsumRHS : (∑ x : α, (Real.cosh (lam * c) + (X x / c) * Real.sinh (lam * c)))
      = (Fintype.card α : ℝ) * Real.cosh (lam * c) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ x : α, (X x / c) * Real.sinh (lam * c))
        = ((∑ x : α, X x) / c) * Real.sinh (lam * c) by
      rw [Finset.sum_div, Finset.sum_mul]]
    rw [hzero, zero_div, zero_mul, add_zero]
  have hsum_le : (∑ x : α, Real.exp (lam * X x))
      ≤ (Fintype.card α : ℝ) * Real.cosh (lam * c) := by
    rw [← hsumRHS]
    exact Finset.sum_le_sum (fun x _ => hchord x)
  have hNpos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hN
  calc uniformExpectation (fun x => Real.exp (lam * X x))
      = (∑ x : α, Real.exp (lam * X x)) / (Fintype.card α : ℝ) := rfl
    _ ≤ ((Fintype.card α : ℝ) * Real.cosh (lam * c)) / (Fintype.card α : ℝ) :=
        div_le_div_of_nonneg_right hsum_le hNpos.le
    _ = Real.cosh (lam * c) := mul_div_cancel_left₀ _ (ne_of_gt hNpos)
    _ ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) := by
        have h := Real.cosh_le_exp_half_sq (lam * c)
        have he : (lam * c) ^ 2 / 2 = lam ^ 2 * c ^ 2 / 2 := by ring
        rwa [he] at h

/-- **指数型均匀期望非负**（`Finset.prod_le_prod` 的第一前提）：
`E_x[e^{φ x}] ≥ 0`（被积函数处处非负）。 -/
theorem uniformExpectation_exp_nonneg {α : Type*} [Fintype α] (φ : α → ℝ) :
    0 ≤ uniformExpectation (fun x => Real.exp (φ x)) :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)) (Nat.cast_nonneg _)

/-- **Chernoff 桥（经典常数，核心引擎）**：把**逐坐标 MGF 界**提升为**和的尾界**
`P( t ≤ x̄ − μ ) ≤ e^{−m t²/(2c²)}`（`x̄ = (Σ_{i<m} X(w i))/m`，
`m` 个样本**独立重复**抽取）。

证明三段：
1. **事件改写**：`{t ≤ (ΣX)/m − μ} = {m·t ≤ Σ(X − μ)}`；
2. **计数马尔可夫（指数型）**：`1_{S ≥ t'} ≤ e^{λ(S−t')}`（`λ > 0`）⟹
   `P(S ≥ t') ≤ e^{−λt'}·E[e^{λS}]`；
3. **独立性 ⟹ MGF 乘积分解**：`E_w[∏_i g(w i)] = ∏_i E[g]`（`Finset.prod_univ_sum`
   的乘积分解，即计数空间的独立性），配 `hmgf` 逐坐标界得
   `E[e^{λS}] ≤ e^{m·λ²c²/2}`——**`m` 仅在此处进入指数**，Chernoff 参数 `λ` 本身不含 `m`。

取 `λ = t/c²` 得指数 `−λ·mt + m·λ²c²/2 = −m t²/(2c²)` —— **常数 2**（非 8）。

**历史缺陷（本定理此前实现为假，已修复；CORRECTIONS B31）**：本定理原先把 Chernoff 参数取为
`λ = m·t/c²`（**含因子 `m`**）。该选择使声称的指数恒等式
`−λ·mt + m·λ²c²/2 = −m t²/(2c²)` **只在 `m ∈ {0,1}` 成立**；对 `m ≥ 2` 为假，
且对 `m ≥ 3` 左侧指数**为正**，于是尾界 `≤ e^{正数} > 1` 成为**空洞界**
（概率界在 > 1 时不含信息）。精确反例（`t = c = 1`）：

| `m` | 真实指数（`λ = m t/c²`） | 原声称 `−m t²/(2c²)` | 判定 |
|:--|:--|:--|:--|
| 2 | `0` | `−1` | 不成立 |
| 3 | `+9/2` | `−3/2` | 不成立（**正指数 ⟹ 界 > 1，空洞**） |
| 4 | `16` | `−2` | 不成立 |
| 6 | `72` | `−3` | 不成立 |

正确参数 `λ = t/c²`（**与 `m` 无关**——`m` 只通过 `m` 次独立重复的 MGF 乘积
`∏_i E[e^{λ(X−μ)}] ≤ e^{m λ²c²/2}` 进入指数）对 `m = 0..6` 全部精确相等。
**注**：该缺陷此前从未被编译暴露（文件从未成功构建过）。

**诚实标注（CORRECTIONS B19）**：本定理的 `c` 是**半径**（`|X − μ| ≤ c`），
调用者应按 B19 传 `c = R = max b (−a)`（`[a,b]` 区间时），
**不是** `(b−a)/2`——后者只在关于 0 对称的区间上成立。 -/
theorem hoeffding_tail_classic_aux {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ) (m : ℕ)
    (hm : 0 < m) (hN : 0 < Fintype.card α) {c : ℝ} (hc : 0 < c)
    (_hbound : ∀ x : α, |X x - μ| ≤ c)
    (hmgf : ∀ lam : ℝ, uniformExpectation (fun x => Real.exp (lam * (X x - μ)))
      ≤ Real.exp (lam ^ 2 * c ^ 2 / 2))
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin m → α => t ≤ (∑ i : Fin m, X (w i)) / m - μ))
      ≤ Real.exp (-(m : ℝ) * t ^ 2 / (2 * c ^ 2)) := by
  -- 事件改写：`{t ≤ (ΣX)/m − μ} = {m·t ≤ Σ(X − μ)}`
  have hset : Finset.univ.filter (fun w : Fin m → α => t ≤ (∑ i : Fin m, X (w i)) / m - μ)
      = Finset.univ.filter (fun w : Fin m → α => (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ)) := by
    apply Finset.filter_congr
    intro w _
    have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hsum : (∑ i : Fin m, X (w i)) / (m : ℝ) - μ
        = (∑ i : Fin m, (X (w i) - μ)) / (m : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, sub_div]
      rw [mul_div_cancel_left₀ μ (ne_of_gt hmR)]
    rw [hsum, le_div_iff₀ hmR]
    constructor <;> intro h <;> linarith
  rw [hset]
  -- 马尔可夫（指数型）：`P(t' ≤ S) ≤ e^{−λt'}·E[e^{λS}]`
  -- 已修复的错误实现：原为 `set lam : ℝ := (m : ℝ) * t / c ^ 2`（见上方 docstring 与
  -- CORRECTIONS B31）。正确 Chernoff 参数是 `t / c^2`——与 `m` 无关。
  set lam : ℝ := t / c ^ 2 with hlam
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos ht (pow_pos hc 2)
  -- 计数马尔可夫：`|{S ≥ t'}|/N ≤ (Σ_w e^{λS(w)})/(N·e^{λt'})`
  have hmarkov : uniformProb (Finset.univ.filter
        (fun w : Fin m → α => (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ)))
      ≤ Real.exp (-(lam * ((m : ℝ) * t)))
        * uniformExpectation (fun w : Fin m → α =>
            Real.exp (lam * ∑ i : Fin m, (X (w i) - μ))) := by
    have hpt : ∀ w : Fin m → α,
        (if (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ) then (1 : ℝ) else 0)
          ≤ Real.exp (lam * (∑ i : Fin m, (X (w i) - μ) - (m : ℝ) * t)) := by
      intro w
      by_cases hw : (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ)
      · rw [if_pos hw]
        have h1 : 0 ≤ ∑ i : Fin m, (X (w i) - μ) - (m : ℝ) * t := by linarith
        calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (lam * (∑ i : Fin m, (X (w i) - μ) - (m : ℝ) * t)) :=
              Real.exp_le_exp.mpr (by nlinarith [hlampos.le, h1])
      · rw [if_neg hw]
        exact Real.exp_nonneg _
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hpt w)
    have hNpos : (0 : ℝ) < (Fintype.card (Fin m → α) : ℝ) := by
      -- `Fintype.card_fun` 给 `card (Fin m → α) = card α ^ card (Fin m)`（**指数是 `card (Fin m)`**，
      -- 不是 `m`）⟹ 必须再 `Fintype.card_fin` 把指数收成 `m`，否则 `pow_pos hN m` 类型不符（v3 L559）。
      rw [Fintype.card_fun, Fintype.card_fin]
      exact Nat.cast_pos.mpr (pow_pos hN m)
    -- 两侧同分母 `N := |Fin m → α|`（`P = card/N`、`E = S/N`），`N > 0`
    -- ⟹ 只需比较**分子**：`card ≤ exp(−λmt)·S`。
    -- （v3 L543 的 unsolved goal 源于旧写法在此留下 `exp·(E·N) = exp·E` 的**假等式**：
    --   多出的 `* N` 因子。此处改为先把右侧分子形式统一，再 `div_le_div_iff_of_pos_right`。）
    have hnum_le : ((Finset.univ.filter (fun w : Fin m → α =>
            (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ))).card : ℝ)
        ≤ Real.exp (-(lam * ((m : ℝ) * t)))
          * ∑ w : Fin m → α, Real.exp (lam * ∑ i : Fin m, (X (w i) - μ)) := by
      rw [show ((Finset.univ.filter (fun w : Fin m → α =>
              (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ))).card : ℝ)
          = ∑ w : Fin m → α,
              (if (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ) then (1 : ℝ) else 0) by
        rw [Finset.sum_boole]]
      calc ∑ w : Fin m → α,
              (if (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ) then (1 : ℝ) else 0)
          ≤ ∑ w : Fin m → α,
              Real.exp (lam * (∑ i : Fin m, (X (w i) - μ) - (m : ℝ) * t)) := hsum
        _ = Real.exp (-(lam * ((m : ℝ) * t)))
              * ∑ w : Fin m → α, Real.exp (lam * ∑ i : Fin m, (X (w i) - μ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun w _ => ?_)
            rw [show lam * (∑ i : Fin m, (X (w i) - μ) - (m : ℝ) * t)
                = -(lam * ((m : ℝ) * t)) + lam * ∑ i : Fin m, (X (w i) - μ) by ring,
              Real.exp_add]
    -- 两侧同除以 `N > 0`：`P = card/N`、`exp·E = (exp·S)/N`
    unfold uniformProb uniformExpectation
    rw [show Real.exp (-(lam * ((m : ℝ) * t)))
          * ((∑ w : Fin m → α, Real.exp (lam * ∑ i : Fin m, (X (w i) - μ)))
            / (Fintype.card (Fin m → α) : ℝ))
        = (Real.exp (-(lam * ((m : ℝ) * t)))
            * (∑ w : Fin m → α, Real.exp (lam * ∑ i : Fin m, (X (w i) - μ))))
          / (Fintype.card (Fin m → α) : ℝ) by
      rw [mul_div_assoc]]
    exact (div_le_div_iff_of_pos_right hNpos).mpr hnum_le
  -- 独立性的 MGF 乘积分解：`E[e^{λΣ}] = ∏_i E[e^{λ(X(w i)−μ)}] ≤ e^{m λ² c²/2}`
  have hprod : uniformExpectation (fun w : Fin m → α =>
        Real.exp (lam * ∑ i : Fin m, (X (w i) - μ)))
      ≤ Real.exp ((m : ℝ) * (lam ^ 2 * c ^ 2 / 2)) := by
    have hfac : ∀ w : Fin m → α,
        Real.exp (lam * ∑ i : Fin m, (X (w i) - μ))
          = ∏ i : Fin m, Real.exp (lam * (X (w i) - μ)) := by
      intro w
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
    have hsplit : uniformExpectation (fun w : Fin m → α =>
          ∏ i : Fin m, Real.exp (lam * (X (w i) - μ)))
        = ∏ _i : Fin m, uniformExpectation (fun x : α => Real.exp (lam * (X x - μ))) := by
      -- 计数空间的独立性：分子 `∑_w ∏_i g(w i) = ∏_i (∑_x g x)`，
      -- 分母 `|Fin m → α| = |α|^m`，右侧 = `∏_i ((∑_x g x)/|α|)`
      -- `Finset.prod_div_distrib` 是**双绑定**形式，对单绑定目标不匹配 ⟹ 改用
      -- 「分子相等 + 同除非零常数」两条独立步骤。
      have hcardN : (Fintype.card (Fin m → α) : ℝ) = ((Fintype.card α : ℝ)) ^ m := by
        rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      -- 注意：`Finset.prod_univ_sum` 是**双绑定** `∑ j ∈ t i` 形式，对单绑定目标不匹配
      -- （实测 `rw` 报模式 `∑ p ∈ ?s.pi ?t, ∏ x ∈ ?s.attach, ...` 找不到）；
      -- 单绑定 `Fintype` 版是 **`Fintype.prod_sum`**（`Mathlib/Algebra/BigOperators/Ring.lean:286`，
      -- 语句 `∏ i, ∑ j, f i j = ∑ x : ∀ i, κ i, ∏ i, f i (x i)`），正是本目标的**反向**；
      -- 名字是 **`Fintype.` 前缀，不是 `Finset.`**（`Finset.prod_sum` 是另一个双绑定引理）。
      have hnum : (∑ w : Fin m → α, ∏ i : Fin m, Real.exp (lam * (X (w i) - μ)))
          = ∏ _i : Fin m, (∑ x : α, Real.exp (lam * (X x - μ))) := by
        rw [← Fintype.prod_sum (κ := fun _ : Fin m => α)
          (f := fun (_ : Fin m) (x : α) => Real.exp (lam * (X x - μ)))]
      unfold uniformExpectation
      rw [hnum, hcardN]
      -- 目标：`(∏_i S i) / |α|^m = ∏_i (S i / |α|)`；右式先化成 `(∏_i S i)/(∏_i |α|)`
      rw [show (∏ _i : Fin m, (∑ x : α, Real.exp (lam * (X x - μ))) / (Fintype.card α : ℝ))
          = (∏ _i : Fin m, (∑ x : α, Real.exp (lam * (X x - μ))))
            / (∏ _i : Fin m, (Fintype.card α : ℝ)) by
        rw [Finset.prod_div_distrib]]
      congr 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- 目标核是未 beta-展开的 lambda，`rw [Finset.sum_congr ...]` 直接匹配会失败
    -- ⟹ 在函数层面做 `funext` 一致替换，再用 `hsplit`。
    rw [show (fun w : Fin m → α => Real.exp (lam * ∑ i : Fin m, (X (w i) - μ)))
        = (fun w : Fin m → α => ∏ i : Fin m, Real.exp (lam * (X (w i) - μ))) from
      funext fun w => hfac w]
    rw [hsplit]
    calc ∏ _i : Fin m, uniformExpectation (fun x : α => Real.exp (lam * (X x - μ)))
        ≤ ∏ _i : Fin m, Real.exp (lam ^ 2 * c ^ 2 / 2) :=
          Finset.prod_le_prod (fun _ _ => uniformExpectation_exp_nonneg _) (fun _ _ => hmgf lam)
      _ = Real.exp ((m : ℝ) * (lam ^ 2 * c ^ 2 / 2)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  -- 指数代数：`−λ·mt + m λ²c²/2 = −m t²/(2c²)`（**仅在 `λ = t/c²` 时成立**，见 B31）
  have hexp : Real.exp (-(lam * ((m : ℝ) * t))) * Real.exp ((m : ℝ) * (lam ^ 2 * c ^ 2 / 2))
      = Real.exp (-(m : ℝ) * t ^ 2 / (2 * c ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hlam]
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc)
    field_simp
    ring
  calc uniformProb (Finset.univ.filter
        (fun w : Fin m → α => (m : ℝ) * t ≤ ∑ i : Fin m, (X (w i) - μ)))
      ≤ Real.exp (-(lam * ((m : ℝ) * t)))
        * uniformExpectation (fun w : Fin m → α =>
            Real.exp (lam * ∑ i : Fin m, (X (w i) - μ))) := hmarkov
    _ ≤ Real.exp (-(lam * ((m : ℝ) * t)))
        * Real.exp ((m : ℝ) * (lam ^ 2 * c ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-(m : ℝ) * t ^ 2 / (2 * c ^ 2)) := hexp

/-! ### 反例（内核可验证）：错误 Chernoff 参数 `λ = m·t/c²` 使界空洞

CORRECTIONS B31 的**可执行证据**。原实现取 `λ = m·t/c²`，声称
`−λ·mt + m·λ²c²/2 = −m t²/(2c²)`。以下两条定理表明该声称在 `m = 3, t = c = 1`
时**为假**，且左侧指数取**正值** `9/2`（故 `exp` 项 `> 1`，尾界不含信息）。 -/

/-- **B31 反例（伪指数 ≠ 经典指数）**：错误参数 `λ = m·t/c²` 在 `m = 3, t = c = 1`
下给出的指数是 `9/2`，而声称值是 `−3/2`——**不相等**，
`field_simp; ring` 在此**必然失败**（这正是缺陷未被 `ring` 抓出的原因：
文件从未成功编译）。 -/
theorem bad_lam_exponent_counterexample :
    -(((3 : ℝ) * 1 / 1 ^ 2) * ((3 : ℝ) * 1)) + (3 : ℝ) * (((3 : ℝ) * 1 / 1 ^ 2) ^ 2 * 1 ^ 2 / 2)
      = 9 / 2
    ∧ -((3 : ℝ) * 1 ^ 2 / (2 * 1 ^ 2)) = -(3 / 2)
    ∧ (9 / 2 : ℝ) ≠ -(3 / 2) := by
  norm_num

/-- **B31 反例（界空洞）**：错误参数下 `m = 3, t = c = 1` 的尾界指数为 `9/2 > 0`，
故右侧 `e^{9/2} > 1`——概率界 `≤ e^{9/2}` 对任何概率分布**恒真因而空洞**。 -/
theorem bad_lam_bound_vacuous :
    1 < Real.exp ((9 : ℝ) / 2) := by
  have h1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  exact lt_trans h1 (Real.exp_lt_exp_of_lt (by norm_num))

/-- **B31 修复的正确性（内核可验证）**：正确参数 `λ = t/c²` 下，`m = 3, t = c = 1`
的指数恰为经典值 `−m t²/(2c²) = −3/2`。 -/
theorem good_lam_exponent {m : ℕ} {t c : ℝ} (hc : c ≠ 0) :
    -(t / c ^ 2 * ((m : ℝ) * t)) + (m : ℝ) * ((t / c ^ 2) ^ 2 * c ^ 2 / 2)
      = -(m : ℝ) * t ^ 2 / (2 * c ^ 2) := by
  field_simp
  ring

/-- **单假设尾界（经典常数，半径版，主交付 B30）**：`α` 有限、`N = |α| > 0`、
`m > 0`、`μ = E[X]`、**半径** `c > 0` 使 `|X x − μ| ≤ c`（`∀ x`），则对 `t > 0`

    `P( t ≤ x̄ − μ ) ≤ e^{−m t²/(2c²)}`

其中 `x̄ = (Σ_{i<m} X(w i))/m` 是 `m` 个**独立重复**样本的均值。

**这是 B30 的主交付**：常数从 `RealHoeffding.hoeffding_tail` 的保守 **8**
收紧到经典的 **2**（指数分母 `2c²` 取代 `8`）——同一 `t` 下新界**严格更强**
（`e^{−mt²/(2c²)} ≤ e^{−mt²/8}` 当 `c ≤ 2`）。

**推导**：把 `mgf_count_le_exp_half_sq`（**任意半径**的零均值 Hoeffding 引理）
作为逐坐标 MGF 界传入 `hoeffding_tail_classic_aux`。

**已修复的继承缺陷（CORRECTIONS B31）**：本定理经 `hoeffding_tail_classic_aux` 依赖
Chernoff 参数 `λ`。该辅助定理此前取 `λ = m·t/c²`（含 `m`）使指数恒等式对 `m ≥ 2` 为假、
对 `m ≥ 3` 给出**正指数**（`t = c = 1, m = 3` 时为 `+9/2`）从而界 `> 1` **空洞**；
现已改为 `λ = t/c²`。**本定理的陈述未变**（如实陈述 `e^{−m t²/(2c²)}`），修复后其证明首次成立。

**诚实标注（CORRECTIONS B19）**：`c` 是**半径**，区间 `[a,b]` 上须取
`c = R = max b (−a)`；`(b−a)²/8` 只为**对称区间**成立，本文件**不用**它。 -/
theorem hoeffding_tail_classic {α : Type*} [Fintype α] {X : α → ℝ} (μ : ℝ) (m : ℕ)
    (hm : 0 < m) (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ)
    {c : ℝ} (hc : 0 < c) (hbound : ∀ x : α, |X x - μ| ≤ c)
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin m → α => t ≤ (∑ i : Fin m, X (w i)) / m - μ))
      ≤ Real.exp (-(m : ℝ) * t ^ 2 / (2 * c ^ 2)) := by
  have hzero : (∑ x : α, (X x - μ)) = 0 := by
    have := sum_eq_card_mul_mean hN hmean
    rw [Finset.sum_sub_distrib, this, Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  refine hoeffding_tail_classic_aux μ m hm hN hc hbound ?_ ht
  exact fun lam => mgf_count_le_exp_half_sq hN hc hbound hzero

/-! ## 主结果七（B30）：经典常数下的并集界 / 选择偏差界 / δ 形式半径

把第六节的经典常数尾界（`e^{−m t²/(2c²)}`）代入原有的并集界与选择偏差链，
得到**常数收紧一个数量级**（`8 → 2`）的完整超参数选择保证。 -/

/-- **经典常数并集界**：对 `k` 个候选的联合坏事件，
`μ{∃h, |empRisk_h − risk_h| ≥ t} ≤ k·(2·e^{−m t²/(2R²)})`。

其中 `R` 是**半径**（`|Z h x − risk_h| ≤ R`，`∀ h x`）——
按 `hoeffding_tail_classic` 的双边化（上尾 + 下尾 + 并集界）得到。
与 `all_deviations_tail`（常数 `8`）相比，本定理把 `8` 换成 `2`。 -/
theorem all_deviations_tail_classic {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (Z : Fin k → α → ℝ) (m : ℕ) (t R : ℝ) (hm : 0 < m) (hN : 0 < Fintype.card α)
    (hR : 0 < R)
    (hbound : ∀ h x, |Z h x - hypRisk Z h| ≤ R) (ht : 0 < t) :
    uniformProb (devEvent Z m t)
      ≤ (k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / (2 * R ^ 2))) := by
  -- 上尾 + 下尾（对 `Z` 与 `−Z` 各用一次单边尾界）+ 并集界
  have hsub : devEvent Z m t ⊆
      Finset.univ.biUnion (fun h : Fin k => singleDevEvent Z m t h) := by
    intro w hw
    rw [devEvent, Finset.mem_filter] at hw
    obtain ⟨-, hwit⟩ := hw
    rcases hwit with ⟨h, hh⟩
    refine Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, ?_⟩
    rw [singleDevEvent, Finset.mem_filter]
    exact ⟨Finset.mem_univ w, hh⟩
  -- 单点双边尾界（经典常数）
  have hsingle : ∀ h : Fin k,
      uniformProb (singleDevEvent Z m t h)
        ≤ 2 * Real.exp (-(m : ℝ) * t ^ 2 / (2 * R ^ 2)) := by
    intro h
    have hmean : uniformExpectation (Z h) = hypRisk Z h := rfl
    -- 上尾
    have hup := hoeffding_tail_classic (X := Z h) (hypRisk Z h) m hm hN hmean hR
      (hbound h) ht
    -- 下尾：对 `Z' := 2μ − Z` 用上尾（`x̄' − μ = −(x̄ − μ)`，半径不变）
    have hdown : uniformProb (Finset.univ.filter (fun w : Fin m → α =>
        t ≤ -((∑ i : Fin m, Z h (w i)) / m - hypRisk Z h)))
        ≤ Real.exp (-(m : ℝ) * t ^ 2 / (2 * R ^ 2)) := by
      have hZmean : uniformExpectation (fun x : α => 2 * hypRisk Z h - Z h x) = hypRisk Z h := by
        -- `∑_x (2μ − Z x) = |α|·2μ − ∑ Z x = |α|·2μ − |α|·μ = |α|·μ`
        have hZ := sum_eq_card_mul_mean hN (hmean)
        have hsum : (∑ x : α, (2 * hypRisk Z h - Z h x))
            = (Fintype.card α : ℝ) * (2 * hypRisk Z h) - ∑ x : α, Z h x := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        -- `|α| ≠ 0`（`hN`）让 `field_simp` 能消去分母；写成 `ne_of_gt` 供其自动使用。
        have hcard : ((Fintype.card α : ℝ)) ≠ 0 := by
          exact_mod_cast (ne_of_gt hN)
        unfold uniformExpectation
        rw [hsum, hZ]
        field_simp [hcard]
        ring
      have hZbound : ∀ x : α, |(2 * hypRisk Z h - Z h x) - hypRisk Z h| ≤ R := by
        intro x
        have hx := hbound h x
        have : (2 * hypRisk Z h - Z h x) - hypRisk Z h = -(Z h x - hypRisk Z h) := by ring
        rw [this, abs_neg]
        exact hx
      -- 注意：**不可**命名为 `h`——那会遮蔽外层 `h : Fin k`，使其后所有 `Z h` 解析失败。
      have hdn := hoeffding_tail_classic (X := fun x => 2 * hypRisk Z h - Z h x)
        (hypRisk Z h) m hm hN hZmean hR hZbound ht
      -- 事件集合改写
      have hset : Finset.univ.filter (fun w : Fin m → α =>
            t ≤ -((∑ i : Fin m, Z h (w i)) / m - hypRisk Z h))
          = Finset.univ.filter (fun w : Fin m → α =>
            t ≤ (∑ i : Fin m, (2 * hypRisk Z h - Z h (w i))) / m - hypRisk Z h) := by
        apply Finset.filter_congr
        intro w _
        have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
        have hsum : (∑ i : Fin m, (2 * hypRisk Z h - Z h (w i))) / (m : ℝ) - hypRisk Z h
            = -((∑ i : Fin m, Z h (w i)) / (m : ℝ) - hypRisk Z h) := by
          have hnum : (∑ i : Fin m, (2 * hypRisk Z h - Z h (w i)))
              = (m : ℝ) * (2 * hypRisk Z h) - ∑ i : Fin m, Z h (w i) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
          rw [hnum]
          field_simp [ne_of_gt hmR]
          ring
        rw [hsum]
      -- `hdn` 的左式是 `(∑ i, (fun x => 2μ − Z x) (w i))/m − μ`（含**未 beta 展开**的 lambda），
      -- 与 `hset` 的**右**式同形 ⟹ 用 `← hset` 把它换回 `hdown` 的左式（`-((∑ Z)/m − μ)`）。
      -- v3 L792 的 rewrite 失败正是方向写反（用了正向 `hset`）。
      rw [← hset] at hdn
      exact hdn
    -- 并集：`{t ≤ |a|} ⊆ {t ≤ a} ∪ {t ≤ −a}`（按 `a` 的符号分类，`|a|` 取 `a` 或 `−a`）
    have hunion : singleDevEvent Z m t h ⊆
        (Finset.univ.filter (fun w : Fin m → α =>
            t ≤ (∑ i : Fin m, Z h (w i)) / m - hypRisk Z h))
        ∪ (Finset.univ.filter (fun w : Fin m → α =>
            t ≤ -((∑ i : Fin m, Z h (w i)) / m - hypRisk Z h))) := by
      intro w hw
      rw [singleDevEvent, Finset.mem_filter] at hw
      obtain ⟨-, hw'⟩ := hw
      -- `singleDevEvent` 用的是 `hypEmpRisk Z m w h`；先把它展开与目标中的商一致
      have hw'' : t ≤ |(∑ i : Fin m, Z h (w i)) / (m : ℝ) - hypRisk Z h| := by
        simpa only [hypEmpRisk] using hw'
      rcases le_or_lt 0 ((∑ i : Fin m, Z h (w i)) / (m : ℝ) - hypRisk Z h) with hnn | hneg
      · -- `a ≥ 0` ⟹ `|a| = a` ⟹ `t ≤ a`
        rw [abs_of_nonneg hnn] at hw''
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw''⟩))
      · -- `a < 0` ⟹ `|a| = −a` ⟹ `t ≤ −a`
        rw [abs_of_neg hneg] at hw''
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw''⟩))
    calc uniformProb (singleDevEvent Z m t h)
        ≤ uniformProb ((Finset.univ.filter (fun w : Fin m → α =>
              t ≤ (∑ i : Fin m, Z h (w i)) / m - hypRisk Z h))
            ∪ (Finset.univ.filter (fun w : Fin m → α =>
              t ≤ -((∑ i : Fin m, Z h (w i)) / m - hypRisk Z h)))) := by
          unfold uniformProb
          exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hunion)
            (Nat.cast_nonneg _)
      _ ≤ uniformProb (Finset.univ.filter (fun w : Fin m → α =>
              t ≤ (∑ i : Fin m, Z h (w i)) / m - hypRisk Z h))
            + uniformProb (Finset.univ.filter (fun w : Fin m → α =>
              t ≤ -((∑ i : Fin m, Z h (w i)) / m - hypRisk Z h))) := by
          unfold uniformProb
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast (Finset.card_union_le _ _))
            (Nat.cast_nonneg _)
      _ ≤ 2 * Real.exp (-(m : ℝ) * t ^ 2 / (2 * R ^ 2)) := by linarith
  calc uniformProb (devEvent Z m t)
      ≤ uniformProb (Finset.univ.biUnion (fun h : Fin k => singleDevEvent Z m t h)) := by
        unfold uniformProb
        exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
          (Nat.cast_nonneg _)
    _ ≤ ∑ h : Fin k, uniformProb (singleDevEvent Z m t h) :=
        union_prob_le_sum (Finset.univ : Finset (Fin k)) (fun h => singleDevEvent Z m t h)
    _ ≤ ∑ _h : Fin k, (2 * Real.exp (-(m : ℝ) * t ^ 2 / (2 * R ^ 2))) :=
        Finset.sum_le_sum (fun h _ => hsingle h)
    _ = (k : ℝ) * (2 * Real.exp (-(m : ℝ) * t ^ 2 / (2 * R ^ 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **经典常数 δ 形式半径（主交付 B30 的收尾）**：取
`t = sqrt(2·log(2k/δ)/m)·R`，则并集界项 `k·(2·e^{−m t²/(2R²)}) ≤ δ`，
即半径 `sqrt(2 log(2k/δ)/m)·R` —— **文献经典量级**
（对照 `selection_bias_expectation_delta` 的 `sqrt(8 log(2k/δ)/m)`，
常数因子从 `√8` 收到 `√2`，即 **2 倍收紧**）。

假设 `0 < δ`、`δ < 2k`（保证 `log(2k/δ) > 0`）。
**诚实标注**：此处给出的是**指数项**的收紧（`hexp`），
不重新陈述整个期望界（调用者可用 `all_deviations_tail_classic`
+ `uniformExpectation_le_eps_add_max_mul_prob` 按原链组合）。 -/
theorem classic_delta_exponent {k m : ℕ} {δ R : ℝ} (hk : 0 < k) (hm : 0 < m)
    (hδ : 0 < δ) (hδk : δ < 2 * (k : ℝ)) (hR : 0 < R) :
    (k : ℝ) * (2 * Real.exp (-(m : ℝ) * (Real.sqrt (2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) * R) ^ 2
        / (2 * R ^ 2))) ≤ δ := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h2k : 0 < 2 * (k : ℝ) := by linarith
  have hq : 0 < 2 * (k : ℝ) / δ := div_pos h2k hδ
  have h1lt : 1 < 2 * (k : ℝ) / δ := (one_lt_div hδ).mpr hδk
  have hlog : 0 < Real.log (2 * (k : ℝ) / δ) := Real.log_pos h1lt
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hrad : 0 < 2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ) :=
    div_pos (mul_pos (by norm_num) hlog) hmR
  have hsq : Real.sqrt (2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) ^ 2
      = 2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ) := Real.sq_sqrt hrad.le
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hRne : R ≠ 0 := ne_of_gt hR
  -- 指数内的代数：`m·(sqrt(2L/m)·R)²/(2R²) = L`
  have harg : (m : ℝ) * (Real.sqrt (2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) * R) ^ 2 / (2 * R ^ 2)
      = Real.log (2 * (k : ℝ) / δ) := by
    rw [mul_pow, hsq]
    field_simp
    ring
  have hexp : Real.exp (-(m : ℝ) * (Real.sqrt (2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) * R) ^ 2
        / (2 * R ^ 2)) = δ / (2 * (k : ℝ)) := by
    rw [show -(m : ℝ) * (Real.sqrt (2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) * R) ^ 2 / (2 * R ^ 2)
        = -((m : ℝ) * (Real.sqrt (2 * Real.log (2 * (k : ℝ) / δ) / (m : ℝ)) * R) ^ 2 / (2 * R ^ 2)) by ring,
      harg, Real.exp_neg, Real.exp_log hq, inv_div]
  rw [hexp]
  -- `k·(2·(δ/(2k))) = δ`：`field_simp` 清分母后**残留** `↑k * (2 * δ) = δ * (2 * ↑k)`（v3 L881 实测），
  -- 故必须再 `ring` 收尾——**不能**只留 `field_simp`（那会报 unsolved goals）。
  rw [show (k : ℝ) * (2 * (δ / (2 * (k : ℝ)))) = δ by
    field_simp
    ring]

end Lattice
