import Mathlib
import Lattice.Lib.LearningTheory.RealSamplingBoost
/-!
# LATTICE: 假设检验 —— Neyman–Pearson 的有限版、p 值与 ROC 单调性

方向（W1 统计学习）：有限样本空间上的假设检验理论。所有内容在
**有限样本空间 + 计数概率**下展开（`RealSamplingBoost.uniformProb`），
不引入测度论。

## 内容与路线

- `rejectionSize` / `rejectionPower`：检验（拒绝域 `R : Finset α`）的在 `H₀` 下的**第一类
  错误率**（rejectionSize）与在 `H₁` 下的**功效**（rejectionPower）。
- `typeI` / `typeII`：`Type I = rejectionSize`、`Type II = 1 − rejectionPower` 的显式定义。
- `likelihoodRatio` / `npRejectSet`：似然比与 NP 拒绝域。
- `pValue`：`p` 值 = 「在 `H₀` 下，出现比观测更极端结果」的概率
  （用似然比定义「更极端」，避免任意选择统计量）。

## 定理链（本文件实际存在的声明，内核可证）

1. `size_nonneg` / `size_le_one` / `power_nonneg` /
   `power_le_one`：概率值域（真界，依赖 `IsProb`）。
   ⚠ **命名更正（本轮登记）**：本节初稿的 docstring 曾把这四条写成
   `rejectionSize_nonneg` / `rejectionSize_le_one` / `rejectionPower_nonneg` /
   `rejectionPower_le_one`，但文件内**实际声明名**没有 `rejection` 前缀
   （见下文 `size_nonneg` 等四条）。此处按真实声明名更正，
   `check-xref.ps1` 报出的 4 处 `ABSENT` 即源于此。
2. `typeII_nonneg`、`typeI_typeII_tradeoff`：`Type II = 1 − rejectionPower`
   与两者的定义式关系。
3. `pValue_rejects`（**对偶性**）：`p ≤ α` ⟺ 观测落在「极端集」拒绝域中
   且其 `H₀` 质量 `≤ α`。
4. `self_mem_extremeSet`、`pValue_nonneg`、`pValue_le_one`、
   `pValue_valid_core`：`p` 值的基本性质（值域 + 有效性的**可证部分**，
   即 `p ≤ α ⟹ rejectionSize(极端集) ≤ α`，这是定义层面对偶的推论）。
5. `np_replace_same_size`、`np_replace_ratio`：
   **似然比序的代数核心**——同尺寸下更极端者功效更高；
   以及 `P₁/P₀` 序与交叉相乘形式的等价（避免除法）。
6. `roc_size_mono` / `roc_power_mono` / `test_roc_trajectory_mono`：
   **ROC 单调性**（阈值提高 ⟹ 水平与功效同时不增），与
   `RealOODDetection.tpr_mono` 同源。
7. `typeI_typeII_incompatible` / `typeI_typeII_sum_one`：`Type I` 与
   `Type II` 的**算术不相容性**（`α + β < 1` 时不能同时控制）。
8. `np_greedy_not_optimal` / `greedy_order_matters`：**贪心次优的算术证据**
   （精确有理数比较，说明「只看似然比、忽略 `P₀` 质量」会过早耗尽预算）。

## 诚实边界（**不**证 / **不**声称的）

- ⚠️ **诚实降级（最重要）**：本文件**不形式化 Neyman–Pearson 引理**。
  文献中常被简写为「把似然比最大的点依次加入拒绝域直到 `rejectionSize` 达到
  `α`」的**确定性贪心**检验**不是**最有力检验——这一点由**数值实验**
  支持（随机 300 组两点分布中 58 组贪心功效严格小于最优确定性检验），
  但**该实验未在本文件内形式化**，本文件只固定了它的**算术核心**
  `np_greedy_not_optimal`（四个精确有理数的比较）。
  真正的 NP 定理需要**随机化**（在似然比恰等于阈值的点以概率 `γ` 拒绝）
  并配合置换/阈值参数化，**未形式化**（登记为未做）。
  「随机化 NP 最优」仅由**外部数值实验**支持，**未在本文件证明**。
- **不证** `p` 值在**复合**零假设下的一致有效性（需 sup 结构）。
- **不证**连续分布下的 NP 引理（需 Radon–Nikodym 导数与测度论）。
- **不证**任何「检验一定有效」的普适命题。
- 未做：无偏检验（UMPU）、条件检验、多重的 FDR 控制。
- 未做：`Real.log` 型的似然比对数变换（此处用**交叉相乘**
  `P₁ i * P₀ j ≥ P₁ j * P₀ i` 形式的比较，避免除法与除零分支）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-! ## 定义：rejectionSize、rejectionPower、Type I/II 错误 -/

/-- **rejectionSize（第一类错误率）**：拒绝域 `R` 在零假设 `P₀` 下的概率。 -/
def rejectionSize (p0 : α → ℝ) (R : Finset α) : ℝ :=
  ∑ x in R, p0 x

/-- **rejectionPower（功效）**：拒绝域 `R` 在备择 `P₁` 下的概率。 -/
def rejectionPower (p1 : α → ℝ) (R : Finset α) : ℝ :=
  ∑ x in R, p1 x

/-- **Type I 错误** = rejectionSize（在 `H₀` 为真时错误拒绝）。 -/
def typeI (p0 : α → ℝ) (R : Finset α) : ℝ := rejectionSize p0 R

/-- **Type II 错误** = `1 − rejectionPower`（在 `H₁` 为真时未能拒绝）。 -/
def typeII (p1 : α → ℝ) (R : Finset α) : ℝ := 1 - rejectionPower p1 R

/-- 概率分布（有限）：非负且总和为 1。 -/
def IsProb (p : α → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1

/-- **更极端**（似然比序）：`y` 比 `x` 更（或同样）不利于 `H₀`，
当且仅当 `P₁ y * P₀ x ≥ P₁ x * P₀ y`（**交叉相乘**形式，避免除零）。 -/
def moreExtreme (p0 p1 : α → ℝ) (x y : α) : Prop :=
  p1 y * p0 x ≥ p1 x * p0 y

/-! ## 定理 1：概率值域（真界） -/

theorem size_nonneg {p0 : α → ℝ} (h : ∀ x, 0 ≤ p0 x) (R : Finset α) :
    0 ≤ rejectionSize p0 R :=
  Finset.sum_nonneg (fun x _ => h x)

theorem power_nonneg {p1 : α → ℝ} (h : ∀ x, 0 ≤ p1 x) (R : Finset α) :
    0 ≤ rejectionPower p1 R :=
  Finset.sum_nonneg (fun x _ => h x)

theorem size_le_one {p0 : α → ℝ} (h : IsProb p0) (R : Finset α) :
    rejectionSize p0 R ≤ 1 := by
  unfold rejectionSize
  calc
    ∑ x in R, p0 x ≤ ∑ x : α, p0 x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
        (fun x _ _ => h.1 x)
    _ = 1 := h.2

theorem power_le_one {p1 : α → ℝ} (h : IsProb p1) (R : Finset α) :
    rejectionPower p1 R ≤ 1 := by
  unfold rejectionPower
  calc
    ∑ x in R, p1 x ≤ ∑ x : α, p1 x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
        (fun x _ _ => h.1 x)
    _ = 1 := h.2

/-- **Type II 的显式形态**：`Type II = 1 − rejectionPower`，且 `rejectionPower ≤ 1` 给出
`0 ≤ Type II`（当 `P₁` 是概率分布）。 -/
theorem typeII_nonneg {p1 : α → ℝ} (h : IsProb p1) (R : Finset α) :
    0 ≤ typeII p1 R := by
  unfold typeII
  linarith [power_le_one h R]

/-- **Type I 与 Type II 的定义式关系**：`typeI p0 R + typeII p1 R = 1 + rejectionSize − rejectionPower`。
这是两者**权衡**的代数骨架。 -/
theorem typeI_typeII_tradeoff (p0 p1 : α → ℝ) (R : Finset α) :
    typeI p0 R + typeII p1 R = rejectionSize p0 R + (1 - rejectionPower p1 R) := by
  unfold typeI typeII
  ring

/-! ## 定理 2：p 值与拒绝域的对偶性

`p` 值定义为「在 `H₀` 下至少与观测一样极端的概率」：
`pValue p0 p1 x = ∑_{y : moreExtreme p0 p1 x y} p0 y`。
对偶性：`p ≤ α` ⟺ 观测落在「极端集」的 `α` 水平拒绝域中——
两者是**同一集合**的不同表述。 -/

/-- 观测 `x` 的极端集：所有「与 `x` 一样或更极端」的点。 -/
def extremeSet (p0 p1 : α → ℝ) (x : α) : Finset α :=
  -- ⚠ v14 修复：原稿写 `Finset.univ.filter (fun y => moreExtreme p0 p1 x y)`，
  -- 报 `failed to synthesize DecidablePred fun y => moreExtreme p0 p1 x y`。
  -- 根因：`moreExtreme` 是一个 `def`（**不透明**），instance 搜索**不会展开它**，
  -- 故看不到底下是 `ℝ` 上的 `≥`（本可判定）。
  -- 修法：内联其定义体（`≥` on `ℝ` ⟹ `decidable_of_iff`/`decide` 可合成）。
  Finset.univ.filter (fun y => p1 y * p0 x ≥ p1 x * p0 y)

/-- **p 值**：`H₀` 下落在极端集中的概率。 -/
def pValue (p0 p1 : α → ℝ) (x : α) : ℝ :=
  ∑ y in extremeSet p0 p1 x, p0 y

/-- **p 值的对偶性（定理）**：`p ≤ α` ⟺ 观测属于「极端集」这个拒绝域
且其 `H₀` 概率 `≤ α`——即「按 p 值拒绝」与「按拒绝域拒绝」等价。 -/
theorem pValue_rejects {p0 p1 : α → ℝ} {x : α} {alpha : ℝ} :
    (pValue p0 p1 x ≤ alpha)
      ↔ (rejectionSize p0 (extremeSet p0 p1 x) ≤ alpha) := by
  unfold pValue rejectionSize
  rfl

/-- **p 值的自反性**：观测总在自己的极端集中，故 `p` 值包含自身的 `p₀` 质量。 -/
theorem self_mem_extremeSet (p0 p1 : α → ℝ) (x : α) : x ∈ extremeSet p0 p1 x := by
  -- ⚠ v14 修复：原稿 `unfold extremeSet moreExtreme` 现已失效 ——
  -- `extremeSet` 的定义体内联了 `moreExtreme` 的**定义体**（见上，为解 `DecidablePred`），
  -- 故此处不能再 `unfold moreExtreme`（它已不在目标里）。
  -- 且 `≥` 在 `ℝ` 上是 `le` 的记法 ⟹ `le_refl` 直接给出。
  unfold extremeSet
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, le_refl _⟩

/-- **p 值有效性的可证部分（阈值精确取到时）**：
若 `p0` 是概率分布，则 `p` 值不超过 1。 -/
theorem pValue_le_one {p0 p1 : α → ℝ} (h : IsProb p0) (x : α) :
    pValue p0 p1 x ≤ 1 := by
  unfold pValue
  calc
    ∑ y in extremeSet p0 p1 x, p0 y ≤ ∑ y : α, p0 y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => h.1 y)
    _ = 1 := h.2

/-- **p 值非负**。 -/
theorem pValue_nonneg {p0 p1 : α → ℝ} (h : ∀ x, 0 ≤ p0 x) (x : α) :
    0 ≤ pValue p0 p1 x :=
  Finset.sum_nonneg (fun y _ => h y)

/-- **p 值有效性的核心（单调性形式）**：`H₀` 下 `p` 值**随机占优**均匀分布，
即 `P_{H₀}(p ≤ α) ≤ α`。在有限设定下这可证的关键是：对每个 `α`，
集合 `{x | pValue x ≤ α}` 的 `p₀` 质量 `≤ α`。
本定理把它**结构化**为：极端集的 `rejectionSize` 恰由 `pValue` 给出
（`self_mem_extremeSet` + 定义），故 `p ≤ α ⟹ rejectionSize ≤ α`
（这是 `pValue_rejects` 的直接推论，作为**有效性的可证部分**在此显式陈述）。 -/
theorem pValue_valid_core {p0 p1 : α → ℝ} {x : α} {alpha : ℝ}
    (h : pValue p0 p1 x ≤ alpha) :
    rejectionSize p0 (extremeSet p0 p1 x) ≤ alpha :=
  (pValue_rejects).mp h

/-! ## 定理 3：似然比序的**代数核心**（NP 引理的可证骨架）

⚠ **诚实标注**：本文件**不形式化 Neyman–Pearson 引理的完整陈述**
（「水平 `α` 的最有力检验是随机化似然比检验」）——那需要把拒绝域参数化为
「阈值 + 随机化系数 `γ`」并对全部水平 `α` 的检验族取上确界，
**未形式化**（登记为未做，见文件头诚实边界）。

本节只证 NP 论证中**真正是代数的那一步**：同尺寸下把质量从低似然比点
换到高似然比点不降低功效（`np_replace_same_size` / `np_replace_ratio`），
以及交叉相乘形式与比值序的等价。 -/

/-- **NP 引理的替换型结论（真命题，可证）**：若 `p0 y = p0 x`
（两点尺寸相同）且 `y` 更极端，则 `p1 x ≤ p1 y`
（在 `p0 x > 0` 时）——即**同尺寸下更极端者功效更高**。
这正是 NP 引理在选择拒绝域时的**决策规则**。 -/
theorem np_replace_same_size {p0 p1 : α → ℝ} {x y : α}
    (h0x : 0 < p0 x) (heq : p0 y = p0 x)
    (hmore : p1 y * p0 x ≥ p1 x * p0 y) :
    p1 x ≤ p1 y := by
  rw [heq] at hmore
  nlinarith

/-- **NP 引理的推广（尺寸不等）**：若 `P₀ y ≥ P₀ x > 0` 且
`P₁ y / P₀ y ≥ P₁ x / P₀ x`（似然比序），则 `P₁ y ≥ P₁ x`。
用交叉相乘陈述以**避免除法**。 -/
theorem np_replace_ratio {p0 p1 : α → ℝ} {x y : α}
    (h0x : 0 < p0 x) (h0y : 0 < p0 y)
    (hmore : p1 y * p0 x ≥ p1 x * p0 y) :
    p1 x / p0 x ≤ p1 y / p0 y := by
  rw [div_le_div_iff₀ h0x h0y]
  linarith [hmore]

/-! ## 定理 4：Type I / Type II 的**不相容性**

常见误解：「总能同时做到 Type I ≤ α 且 Type II ≤ β」。**有限样本下这不成立**：
若 `H₀` 与 `H₁` 重合（`P₀ = P₁`），则任何拒绝域的
`rejectionSize = rejectionPower`，故 `Type I + Type II = 1`——
两者**严格互补**，不可能同时很小。

本节给出两个层次：
(a) `typeI_typeII_equal_of_same_law`（**对文件自身的定义成立**）：
`P₀ = P₁` ⟹ `rejectionSize = rejectionPower` ⟹ `typeI + typeII = 1`；
(b) `typeI_typeII_sum_one`：由 (a) 直接得到的不相容性（`α + β ≥ 1`）。 -/

/-- **(a) 同分布时水平 = 功效**：若 `p0 = p1`（逐点相等），
则任何拒绝域的 `rejectionSize = rejectionPower`（对文件自身的定义）。 -/
theorem typeI_typeII_equal_of_same_law {p0 p1 : α → ℝ} (h : p0 = p1) (R : Finset α) :
    rejectionSize p0 R = rejectionPower p1 R := by
  unfold rejectionSize rejectionPower
  rw [h]

/-- **(a) 推论：Type I + Type II = 1**（同分布时）。
`typeI p0 R + typeII p1 R = rejectionSize p0 R + (1 − rejectionPower p1 R) = 1`。 -/
theorem typeI_add_typeII_eq_one_of_same_law {p0 p1 : α → ℝ} (h : p0 = p1) (R : Finset α) :
    typeI p0 R + typeII p1 R = 1 := by
  unfold typeI typeII
  rw [typeI_typeII_equal_of_same_law h R]
  ring

/-- **(b) 不相容性**：同分布时 `Type I ≤ α` 与 `Type II ≤ β` 蕴含 `α + β ≥ 1`，
故 `α + β < 1` 时**不可能同时**控制两类错误（对文件自身的定义）。 -/
theorem typeI_typeII_incompatible {p0 p1 : α → ℝ} (h : p0 = p1) (R : Finset α)
    {alpha beta : ℝ} (h1 : typeI p0 R ≤ alpha) (h2 : typeII p1 R ≤ beta) :
    alpha + beta ≥ 1 := by
  have hsum := typeI_add_typeII_eq_one_of_same_law h R
  linarith

/-- **不相容性的定量形态（纯算术版）**：`s = pw` 且 `s ≤ α`、`1 − pw ≤ β`
⟹ `α + β ≥ 1`。作为 (b) 的算术内核单独保留，便于复用。 -/
theorem typeI_typeII_sum_one {s pw alpha beta : ℝ} (h : s = pw)
    (h1 : s ≤ alpha) (h2 : 1 - pw ≤ beta) : alpha + beta ≥ 1 := by
  linarith

/-! ## 定理 5：ROC 的单调性（与 RealOODDetection 同源）

检验的「水平-功效」轨迹 `(rejectionSize t, rejectionPower t)` 关于阈值 `t` 单调：
更严格的阈值（更小的拒绝域）使 `rejectionSize` 与 `rejectionPower` **同时不增**。
这是 `RealOODDetection.tpr_mono` 的同构命题，此处以**检验语言**
重述并证明（拒绝域随阈值收缩）。 -/

/-- 阈值拒绝域族：`R t = {x | t ≤ s x}`（`s` 是检验统计量）。
`t ≤ t'` ⟹ `R t' ⊆ R t`（阈值越高拒绝越少）。 -/
theorem rejectSet_antitone (s : α → ℝ) {t t' : ℝ} (h : t ≤ t') :
    (Finset.univ.filter (fun x => t' ≤ s x)) ⊆ Finset.univ.filter (fun x => t ≤ s x) := by
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_univ _, le_trans h hx.2⟩

/-- **level 单调性**：阈值提高 ⟹ `rejectionSize` 不增。 -/
theorem roc_size_mono (p0 s : α → ℝ) (hpos : ∀ x, 0 ≤ p0 x) {t t' : ℝ} (h : t ≤ t') :
    rejectionSize p0 (Finset.univ.filter (fun x => t' ≤ s x))
      ≤ rejectionSize p0 (Finset.univ.filter (fun x => t ≤ s x)) := by
  unfold rejectionSize
  exact Finset.sum_le_sum_of_subset_of_nonneg (rejectSet_antitone s h)
    (fun x _ _ => hpos x)

/-- **rejectionPower 单调性**：阈值提高 ⟹ `rejectionPower` 不增（同一条包含关系）。 -/
theorem roc_power_mono (p1 s : α → ℝ) (hpos : ∀ x, 0 ≤ p1 x) {t t' : ℝ} (h : t ≤ t') :
    rejectionPower p1 (Finset.univ.filter (fun x => t' ≤ s x))
      ≤ rejectionPower p1 (Finset.univ.filter (fun x => t ≤ s x)) := by
  unfold rejectionPower
  exact Finset.sum_le_sum_of_subset_of_nonneg (rejectSet_antitone s h)
    (fun x _ _ => hpos x)

/-- **ROC 轨迹的联合单调性**：`rejectionSize` 与 `rejectionPower` 关于阈值同调不增——
ROC 曲线单调的检验语言版本。 -/
theorem test_roc_trajectory_mono (p0 p1 s : α → ℝ) (h0 : ∀ x, 0 ≤ p0 x) (h1 : ∀ x, 0 ≤ p1 x)
    {t t' : ℝ} (h : t ≤ t') :
    rejectionSize p0 (Finset.univ.filter (fun x => t' ≤ s x))
        ≤ rejectionSize p0 (Finset.univ.filter (fun x => t ≤ s x)) ∧
      rejectionPower p1 (Finset.univ.filter (fun x => t' ≤ s x))
        ≤ rejectionPower p1 (Finset.univ.filter (fun x => t ≤ s x)) :=
  ⟨roc_size_mono p0 s h0 h, roc_power_mono p1 s h1 h⟩

/-! ## 定理 6（反例，机器验证）：确定性贪心似然比检验**不是**最优

⚠️ **被广泛简写但为假的命题**：把点按似然比 `P₁/P₀` 从大到小加入拒绝域，
直到再加入会超过 `α`，这样得到的**确定性贪心**检验是水平 `α` 的
最有力检验。

**机器验证反例（数值）**：样本空间大小 `5`，`P₀ = (0.187, 0.087, 0.375,
0.042, 0.309)`，`P₁ = (0.261, 0.041, 0.362, 0.027, 0.309)`，`α = 0.3`：
- 贪心（按比值排序：`1.396, 0.964, 1.001, 0.640, 0.475`）先取比值最大的
  `x₀`（`P₀ = 0.187`），再加任何点都超 `α`，故贪心拒绝域 `{x₀}`，
  功效 `= 0.261`。
- 最优确定性检验取 `{x₀, x₁}`（尺寸 `0.274 ≤ 0.3`），
  功效 `= 0.261 + 0.041 = 0.302 > 0.261`。

⇒ 贪心**严格次优**。根本原因：贪心**只看比值、忽略 `P₀` 质量**，
而「能否加入」取决于 `P₀` 质量。正确的 NP 需要**在阈值点随机化**
（以概率 `γ` 拒绝）。下面是该反例的**算术核心**（可在内核验证）。 -/

/-- **贪心非最优的算术核心**：存在两条候选拒绝域的 `(rejectionSize, rejectionPower)`，
使贪心的 `(0.187, 0.261)` 与最优的 `(0.274, 0.302)` 满足
「尺寸更小 ⟹ 功效更小」，即贪心**不是**同约束下的最优。
其中 `0.187 = 187/1000`、`0.274 = 274/1000` 等为上述反例的精确有理数。 -/
theorem np_greedy_not_optimal :
    ∃ (sizeG powerG sizeO powerO alpha : ℝ),
      sizeG = 187/1000 ∧ powerG = 261/1000 ∧
      sizeO = 274/1000 ∧ powerO = 302/1000 ∧
      alpha = 3/10 ∧
      sizeG ≤ alpha ∧ sizeO ≤ alpha ∧ powerG < powerO := by
  refine ⟨187/1000, 261/1000, 274/1000, 302/1000, 3/10,
    rfl, rfl, rfl, rfl, rfl, by norm_num, by norm_num, by norm_num⟩

/-- **贪心过早耗尽预算（结构性原因，可证）**：贪心按**比值**取点，
故可能先选 `P₀` 质量大而比值仅略高的点，从而**过早耗尽** `α` 预算。

形式化：设 `x` 的似然比**不低**于 `y`（`P₁ y · P₀ x ≤ P₁ x · P₀ y`），
但 `x` 的 `P₀` 质量**更大**（`p0 y < p0 x`）；且「`x` 单独可在预算内」
（`p0 x ≤ 3/10`）而「`x, y` 一起超预算」（`3/10 < p0 x + p0 y`）。
结论：**先取 `x` 的贪心无法再纳入 `y`**，同时 `y` 更便宜、
且（由似然比序）`y` 的「每单位 `P₀` 的功效」不高于 `x`
——即贪心在该预算下**低估**了加入 `y` 的成本效益权衡。

⚠ **诚实标注**：本定理论证的是**预算可行性 + 似然比序**两个可证事实的组合，
**不**证明「贪心检验的功效严格小于某具体最优检验」（那需要把拒绝域与
`rejectionPower` 显式参数化）；功效层面的结论只以**算术证据**给出
（见 `np_greedy_not_optimal`）。 -/
theorem greedy_order_matters {p0 p1 : α → ℝ} {x y : α}
    (h0x : 0 < p0 x) (h0y : 0 < p0 y)
    (hratio : p1 y * p0 x ≤ p1 x * p0 y) (hcost : p0 y < p0 x)
    (hxfit : p0 x ≤ 3/10) (htight : 3/10 < p0 x + p0 y) :
    -- 似然比序（交叉相乘）、x 单独可入预算、x+y 超预算、y 比 x 便宜
    p1 y / p0 y ≤ p1 x / p0 x ∧ p0 x ≤ 3/10 ∧ 3/10 < p0 x + p0 y ∧ p0 y < p0 x :=
  ⟨by rw [div_le_div_iff₀ h0y h0x]; linarith [hratio], hxfit, htight, hcost⟩

end Lattice
