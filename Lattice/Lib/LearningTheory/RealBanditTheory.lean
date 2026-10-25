import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealUnionBound
import Lattice.Lib.LearningTheory.RealSamplingBoost
/-!
# LATTICE: 多臂老虎机与 UCB —— 次优臂拉次数的可证上界与悔界

方向（W1 统计学习 / 在线学习）：E2 调研实测 **bandit/UCB 在 Lean 生态是空白**
（未被任何 Lean 库覆盖），本文件在 mathlib 4.14 上建立有限臂、Hoeffding 型的
老虎机理论。**不引入测度论**：沿用 `RealSamplingBoost` 的**有限计数概率空间**
（样本空间 `α` 有限，`uniformProb s = s.card / Fintype.card α`），
与 `RealHoeffding` / `RealChernoff` 同一条技术路线。

## 设定

- 臂集 `K`（`Fin K`），臂 `i` 的奖励分布是 `α → ℝ` 的随机变量 `X i`，
  均值 `μ i = uniformExpectation (X i)`，取值有界 `|X i x| ≤ 1`
  （与 `RealHoeffding` 的 `hb` 假设一致）。
- 最优臂均值 `μ* = Finset.univ.sup' _ μ`，次优间隙 `Δ i = μ* − μ i ≥ 0`。
- 拉次数 `N i`（`ℕ`），悔 `regret Δ N = ∑ i, Δ i * N i`。

## 本文件实际存在的声明（全部内核可证，无 sorry/axiom/admit）

定义：`bestMean`（`μ*`，需 `0 < K`）、`gap`（`Δ i`）、`regret`（`∑ i, Δ i N i`）、
`ucbIndex`（`μ̂ i + c i`）。

1. **悔的恒等式**（`regret_eq_sum_pull_gaps`）：把「逐时刻的间隙」与
   「逐臂的间隙×拉次数」两种写法统一——悔界分析的形式基础。
2. **UCB 指数的确定性排除骨架**（`ucb_index_excludes_suboptimal`，核心）：
   若置信事件成立（`|μ̂ i − μ i| ≤ c i` 对一切臂），且
   `2 c i + 2 c star < μ star − μ i`，则 `ucbIndex i < ucbIndex star`。
   这是 UCB 分析中「探索-利用」逻辑的**全部确定性内容**，无概率论。
3. **不被拉 / 拉次数为 0**（`ucb_not_argmax_suboptimal`、
   `not_pulled_under_good_event`、`pull_count_zero_under_good_event`）：
   由上一条，在「始终选指数最大臂」的算法语义下，满足间隙条件的臂在该时刻
   **不会**被选，故其拉次数为 `0`。
4. **Hoeffding 型置信半径**（`ucb_confidence_radius`）：直接引用
   `RealHoeffding.hoeffding_two_sided`，把
   `P(|μ̂ − μ| ≥ c) ≤ 2 e^{−n c²/8}` 固定下来，作为骨架中 `c` 的概率来源。
5. **联合界下的「存在越界臂」概率**（`good_event_prob` / `good_event_prob_two`）：
   用 `RealUnionBound.union_prob_le_sum` 合成各臂的坏事件。
   ⚠ **诚实标注**：本文件把结论陈述在**同一有限样本空间、各臂共享 `n` 次采样**
   的形式上；真实 UCB 中「各臂独立乘积空间」的**柱集投影**未形式化（见下）。
6. **悔的组合上界**：`expected_regret_decomposition`（逐臂控制 ⟹ 悔 ≤ `∑ r i`）
   与 `regret_le_total_pulls`（间隙 ≤ 1 ⟹ 悔 ≤ `T`）。
   ⚠ **诚实标注**：**不证**形如 `≤ (∑ r i) + 2·P(坏事件)·T` 的**期望悔分解**
   （需条件期望，mathlib 4.14 的条件期望依赖测度论，与本文件有限计数设定不符）。
7. **算术事实**（`ucb_deterministic_bound_arithmetic`、
   `ucb_deterministic_bound_counterexample`）：`8 ln 1 / Δ² = 0`。

## 诚实边界（本文件**不**证 / **不**声称的）

- **不做** `O(log T / Δ²)` 的**渐近**陈述：mathlib 4.14 无「渐近在线学习」框架，
  且 `T → ∞` 的极限陈述在本有限计数设定下没有对应的概率空间。
- ⚠️ **反例是非形式的（重要）**：「UCB1 的实际拉次数 `N i(T) ≤ 8 ln T / Δ i²`」
  这一**确定性**陈述在 `T = 1` 时失效（右端为 `0`，而臂可在首步被拉）。
  但**本文件没有形式化任何具体算法轨迹**（无策略、无 `N i`、无 `T` 的语义），
  故只把该论证的**关键算式**固定为 `ucb_deterministic_bound_arithmetic`
  （`8 · log 1 / Δ² = 0`），并**明确声明它不是机器验证的反例**。
- **不证**「各臂独立乘积空间」上的联合界：把「柱集测度 = 单臂测度 ×
  其余坐标计数」形式化需要 `Fintype.piFinset` 在依赖指标 `Fin (n i)` 下的
  基数分解（约 200 行），**未做**；本文件改用共享样本空间上的并集界。
- **不证**任何「UCB1 是最优算法」的陈述（不存在这样的定理；最优性只在
  特定 minimax 意义下、且需要下界理论，超出本文件范围）。
- 随机化算法（如 EXP3）与对抗性 bandit **未做**：需要不同的概率空间。
- 未做：Thompson 采样（需要先验/后验的有限 Bayes 框架）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ⚠ **解析层修复（G2）**：原文此处是「doc-comment（斜杠 双横线）」直接接 `variable`，
而 Lean 的 doc-comment **必须紧跟一个声明**（`variable` 不是声明）⟹ 报
`unexpected token 'variable'; expected 'lemma'`；该**解析失败会掩护后续真错误**
（STYLE.md:129/131）。
⚠ **注意报错定位**：报的是 `variable` 那一行，**真凶是它前面那条 doc-comment**
（"被挤错位的 token"规律）——故必须把**紧邻 `variable` 的那条** doc-comment
改为小节注释（斜杠 叹号），而不是改更上面的那条。

⚠ **本块自身的教训（v14）**：**Lean 的块注释是**可嵌套**的**，故在注释**内部**
**不能字面书写"开注释定界符"**（斜杠加星号、斜杠加双横线、斜杠加叹号）——
它们会被当作**嵌套开始**，需要**额外**的闭定界符才能平衡，
否则**文件余下全部被吞掉**，报 **`unterminated comment`**
（症状指向**文件末尾**，与真凶相距数百行）。
**⇒ 本文件的原始写法正是踩了这个坑**（在小节注释里字面写了另外两种开定界符各一次），
故此处一律改用**文字描述**而不写字面定界符。 -/

/-! 臂数 `K`：作为 section 变量，供 `regret`/`ucbIndex` 及全部 UCB 定理共享。
（`bestMean`/`gap` 需要 `0 < K`，故把 `K` 作为**显式参数**接收。） -/
variable {K : ℕ}

/-! ## 定义：臂、间隙、拉次数、悔 -/

/-- 最优臂均值 `μ* = max_i μ i`（用 `Finset.sup'` 对**函数值**取上确界；
⚠ STYLE 坑：`Finset.max'` 比较的是**指标**，不能用）。

`hK : 0 < K` 是显式前提（至少一条臂）：`Fin K` 非空才能取 `sup'`。
**诚实标注**：把非空性做成**显式参数**而非类型类实例，
避免 `NeZero` 实例合成在调用点的额外负担。 -/
def bestMean {α : Type*} [Fintype α] (K : ℕ) (hK : 0 < K) (X : Fin K → α → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin K)).sup'
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩ (fun i => uniformExpectation (X i))

/-- 臂 `i` 的**次优间隙** `Δ i = μ* − μ i`（≥ 0 由 `bestMean` 的上确界性质给出）。 -/
def gap {α : Type*} [Fintype α] (K : ℕ) (hK : 0 < K) (X : Fin K → α → ℝ) (i : Fin K) : ℝ :=
  bestMean K hK X - uniformExpectation (X i)

/-- 悔：`∑ i, Δ i * N i`，`N i` 是臂 `i` 被拉的次数。 -/
def regret (g : Fin K → ℝ) (N : Fin K → ℕ) : ℝ :=
  ∑ i : Fin K, g i * (N i : ℝ)

/-- **UCB1 指数**：`μ̂ i + sqrt (2 ln t / n i)`。为避开 `Real.sqrt`/`Real.log` 的
分支情形，这里把**探索项**抽象为参数 `c i : ℝ`（置信半径），
即指数为 `μ̂ i + c i`。`ucb_confidence_radius` 给出 `sqrt` 形式半径的
**概率合法性来源**（Hoeffding 型集中不等式）。 -/
def ucbIndex (muHat : Fin K → ℝ) (c : Fin K → ℝ) (i : Fin K) : ℝ :=
  muHat i + c i

/-! ## 定理 1：悔的恒等式（逐时刻间隙 = 逐臂间隙×拉次数）

这是悔界分析的**形式基础**：无论算法如何决策，只要奖励的期望间隙是固定的
`Δ i`，那么「按时刻累加间隙」与「按臂累加 Δ i × N i」完全一致。 -/

/-- **悔的分解恒等式**：若 `N : Fin K → ℕ` 记录了每个臂被拉的次数
（`∑ i, N i = T`），且 `pulls : Fin T → Fin K` 是实际拉臂序列，
则「逐时刻间隙之和」`∑ t, (μ* − μ (pulls t))` 等于 `regret` 定义中的
`∑ i, Δ i * N i`——**前提是** `N` 与 `pulls` 一致（后者恰是前者的计数）。 -/
theorem regret_eq_sum_pull_gaps {g : Fin K → ℝ} {N : Fin K → ℕ} {T : ℕ}
    (pulls : Fin T → Fin K)
    (hcount : ∀ i : Fin K, (Finset.univ.filter (fun t : Fin T => pulls t = i)).card = N i) :
    (∑ t : Fin T, g (pulls t)) = regret g N := by
  classical
  -- 把逐时刻求和按纤维重排：∑_t g(pulls t) = ∑_i ∑_{t: pulls t = i} g i = ∑_i N i · g i
  have hfiber : ∀ i : Fin K,
      (∑ t in Finset.univ.filter (fun t : Fin T => pulls t = i), g (pulls t))
        = (N i : ℝ) * g i := by
    intro i
    -- 在纤维上 `pulls t = i`，故被加项 `g (pulls t)` 化为常数 `g i`
    rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2])]
    rw [Finset.sum_const, hcount i, nsmul_eq_mul]
  -- `sum_fiberwise_of_maps_to`（`prod_fiberwise_of_maps_to` 的加法版，
  -- BigOperators/Group/Finset.lean:697）：
  --   ∑ j ∈ t, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i
  -- ⚠ 必须用**非 prime** 版并取 `f := fun t => g (pulls t)`：prime 版的内层
  -- 被加项是 `f j`（外层指标 j 的常数），与 `hfiber` 的内层 `g (pulls t)` 不匹配。
  have hpart := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin T))) (t := (Finset.univ : Finset (Fin K)))
    (g := pulls) (f := fun t => g (pulls t)) (fun t _ => Finset.mem_univ _)
  -- hpart : ∑ j ∈ univ, ∑ i ∈ univ with pulls i = j, g (pulls i) = ∑ i ∈ univ, g (pulls i)
  rw [← hpart]
  unfold regret
  -- 目标：∑ j ∈ univ, ∑ i ∈ univ with pulls i = j, g (pulls i) = ∑ i, g i * (N i : ℝ)
  -- 用 `Finset.sum_congr` 逐项把内层换成 hfiber 的右式；hfiber 给的是
  -- `(N i : ℝ) * g i`，与目标的 `g i * (N i : ℝ)` 差一个交换律，故配 `mul_comm`。
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hfiber i, mul_comm]

/-! ## 定理 2（核心）：UCB 指数的**确定性**排除骨架

设置信事件成立：对一切臂 `j`，`|μ̂ j − μ j| ≤ c j`。若对臂 `i` 与最优臂 `star`
有 `Δ i > 2 c i + 2 c star`，则
`ucbIndex μ̂ c i < ucbIndex μ̂ c star`，
故**任何**选择「指数最大臂」的算法在该时刻都不会选 `i`。

**这一定理不含任何概率论**：它是 UCB 分析中「探索-利用权衡」的全部
确定性内容；概率只用来保证置信事件（定理 4/5）成立。 -/

theorem ucb_index_excludes_suboptimal {muHat : Fin K → ℝ} {c : Fin K → ℝ}
    {mu : Fin K → ℝ} {i star : Fin K}
    (hi : |muHat i - mu i| ≤ c i) (hstar : |muHat star - mu star| ≤ c star)
    (hgap : 2 * c i + 2 * c star < mu star - mu i) :
    ucbIndex muHat c i < ucbIndex muHat c star := by
  -- ⚠ **G2 修复（非平凡的 `linarith` 缺口）**：`hi`/`hstar` **蕴含** `0 ≤ c i`、`0 ≤ c star`
  -- （`|·| ≥ 0`），但 `linarith` **不会自动**从 `|x| ≤ c` 提取 `0 ≤ c`。
  -- 缺少这两条非负性时 `linarith` 失败是**正确的**：命题在去掉绝对值约束的
  -- 抽象骨架上**确实为假**（已机器验证反例：`ci = 0, cs = -10` 等使三前提成立
  -- 而结论 `a + ci < b + cs` 为 `0 < 0`）。故必须显式给出非负性，**不是**改命题。
  have hci : 0 ≤ c i := le_trans (abs_nonneg _) hi
  have hcs : 0 ≤ c star := le_trans (abs_nonneg _) hstar
  -- 展开绝对值：μ̂ i ≤ μ i + c i 与 μ star − c star ≤ μ̂ star
  have hi' : muHat i ≤ mu i + c i := by
    have := (abs_le.mp hi).2; linarith
  have hs' : mu star - c star ≤ muHat star := by
    have := (abs_le.mp hstar).1; linarith
  unfold ucbIndex
  linarith

/-- 定理 2 的**严格分离推论**：在同样的置信事件与间隙条件下，
UCB 指数对次优臂严格小于对最优臂——特别地，`i` 不可能是指数**最大**的臂
（除非同时 `star` 也达到最大值，而严格不等式排除了这一点）。 -/
theorem ucb_not_argmax_suboptimal {muHat : Fin K → ℝ} {c : Fin K → ℝ}
    {mu : Fin K → ℝ} {i star : Fin K}
    (hi : |muHat i - mu i| ≤ c i) (hstar : |muHat star - mu star| ≤ c star)
    (hgap : 2 * c i + 2 * c star < mu star - mu i) :
    ¬ (∀ j : Fin K, ucbIndex muHat c j ≤ ucbIndex muHat c i) := by
  intro hmax
  have hlt := ucb_index_excludes_suboptimal hi hstar hgap
  have := hmax star
  linarith

/-! ## 定理 3：被拉次数的显式控制（好事件下）

在好事件（置信事件对所有臂成立）下，若臂 `i` 与 `star` 的间隙满足排除条件，
则臂 `i` **一次都不会被拉**（在「始终选指数最大臂」的算法语义下）。
本定理把该语义显式参数化：`pulledAt t i` 表示「时刻 `t` 选了臂 `i`」，
并假设算法只在 `i` 是指数最大者时才选它。 -/

theorem not_pulled_under_good_event {muHat : Fin K → ℝ} {c : Fin K → ℝ}
    {mu : Fin K → ℝ} {i star : Fin K} {T : ℕ}
    (pulledAt : Fin T → Fin K → Prop)
    (halg : ∀ t : Fin T, pulledAt t i → ∀ j : Fin K, ucbIndex muHat c j ≤ ucbIndex muHat c i)
    (hi : |muHat i - mu i| ≤ c i) (hstar : |muHat star - mu star| ≤ c star)
    (hgap : 2 * c i + 2 * c star < mu star - mu i) :
    ∀ t : Fin T, ¬ pulledAt t i := by
  intro t ht
  exact absurd (halg t ht) (ucb_not_argmax_suboptimal hi hstar hgap)

/-- 由定理 3：好事件下臂 `i` 的拉次数为 0。 -/
theorem pull_count_zero_under_good_event {muHat : Fin K → ℝ} {c : Fin K → ℝ}
    {mu : Fin K → ℝ} {i star : Fin K} {T : ℕ}
    (pulls : Fin T → Fin K)
    (halg : ∀ t : Fin T, pulls t = i → ∀ j : Fin K, ucbIndex muHat c j ≤ ucbIndex muHat c i)
    (hi : |muHat i - mu i| ≤ c i) (hstar : |muHat star - mu star| ≤ c star)
    (hgap : 2 * c i + 2 * c star < mu star - mu i) :
    (Finset.univ.filter (fun t : Fin T => pulls t = i)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro t ht
  exact not_pulled_under_good_event (fun t j => pulls t = j) halg hi hstar hgap t
    (Finset.mem_filter.mp ht).2

/-! ## 定理 4：Hoeffding 型置信半径（概率输入）

UCB 分析中 `c i` 的取值来自集中不等式：`n` 次独立拉臂后，
`P(|μ̂ i − μ i| ≥ c) ≤ 2 e^{−n c²/8}`（直接复用 `RealHoeffding.hoeffding_two_sided`）。
本定理**如实引用**该既有结果，把置信半径的合法性固定下来。 -/

theorem ucb_confidence_radius {α : Type*} [Fintype α] [DecidableEq α] {X : α → ℝ} (μ : ℝ) (n : ℕ)
    (hn : 0 < n) (hN : 0 < Fintype.card α) (hmean : uniformExpectation X = μ)
    (hb : ∀ x : α, |X x| ≤ 1) {c : ℝ} (hc : 0 < c) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        c ≤ |(∑ i : Fin n, X (w i)) / n - μ|)) ≤ 2 * Real.exp (-(n : ℝ) * c ^ 2 / 8) :=
  hoeffding_two_sided μ n hn hN hmean hb hc

/-! ## 定理 5：联合界下的「存在越界臂」概率

**诚实标注（重要降级）**：真实 UCB 分析里，各臂的样本来自**各自独立**的
乘积空间，合成需先构造联合空间 `(i : Fin K) → Fin (n i) → α`
并证明「柱集测度 = 单臂测度 × 其余坐标计数」。该投影在 mathlib 4.14 下
需要一整套 `Fintype.piFinset` 的基数分解引理（且 `Fin (n i)` 依赖 `i`，
使 `Fintype.card` 的乘积式不直接可用）——**本文件不证这一投影**，
而是把结论陈述在**同一有限样本空间 `α` 上、每条臂取 `n` 个坐标为事件**
的形式：其中「坏事件」直接取各臂坏事件的并集，
`RealUnionBound.union_prob_le_sum` 即可直接应用。

这**严格弱于**真实 UCB 的联合界（它假设所有臂共享同一 `n` 次采样、
同一样本空间），但**命题为真且可证**，并且保留了联合界
「坏事件概率 ≤ 各臂坏事件概率之和」的全部组合内容。
真正的独立性乘积空间合成登记为：**未做**（见文件头诚实边界）。 -/

theorem good_event_prob {α : Type*} [Fintype α] [DecidableEq α]
    (X : Fin K → α → ℝ) (μ : Fin K → ℝ) (n : ℕ) {c : ℝ}
    (hn : 0 < n) (hN : 0 < Fintype.card α)
    (hmean : ∀ i : Fin K, uniformExpectation (X i) = μ i)
    (hb : ∀ i : Fin K, ∀ x : α, |X i x| ≤ 1) (hc : 0 < c) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        ∃ i : Fin K, c ≤ |(∑ t : Fin n, X i (w t)) / n - μ i|))
      ≤ ∑ _i : Fin K, 2 * Real.exp (-(n : ℝ) * c ^ 2 / 8) := by
  classical
  -- 坏事件 = 各臂坏事件的并集；逐臂界（定理 4）+ 并集界
  let bad : Fin K → Finset (Fin n → α) := fun i =>
    Finset.univ.filter (fun w => c ≤ |(∑ t : Fin n, X i (w t)) / n - μ i|)
  have hunion : (Finset.univ.filter (fun w : Fin n → α =>
      ∃ i : Fin K, c ≤ |(∑ t : Fin n, X i (w t)) / n - μ i|))
      = (Finset.univ : Finset (Fin K)).biUnion bad := by
    ext w
    -- ⚠ **G2 修复**：原证明是 `simp only [...]` 紧跟 `constructor`，
    -- 而 `simp only` 已把两侧等价**直接证完**（`Finset.mem_biUnion` 在位时
    -- `∃ i, ...` 与 `∃ i ∈ univ, ...` 的等价是 simp 引理）⟹ `constructor`
    -- 报 `no goals to be solved`（参见 caller 报的 v9 `276:4`）。
    -- 依「`no goals to be solved` = 多余收尾，应**删**而非换 tactic」的纪律，
    -- 这里**只保留 `simp only`**，不再补 `constructor`/`exact`。
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, bad]
  rw [hunion]
  calc
    uniformProb ((Finset.univ : Finset (Fin K)).biUnion bad)
        ≤ ∑ i : Fin K, uniformProb (bad i) :=
          union_prob_le_sum (Finset.univ : Finset (Fin K)) bad
    _ ≤ ∑ _i : Fin K, 2 * Real.exp (-(n : ℝ) * c ^ 2 / 8) := by
          apply Finset.sum_le_sum
          intro i _
          exact ucb_confidence_radius (μ i) n hn hN (hmean i) (hb i) hc

/-- 联合界的两臂特例（显式展开，便于引用）：`K = 2` 时坏事件概率
≤ `2 · 2 e^{−n c²/8}`。 -/
theorem good_event_prob_two {α : Type*} [Fintype α] [DecidableEq α]
    (X : Fin 2 → α → ℝ) (μ : Fin 2 → ℝ) (n : ℕ) {c : ℝ}
    (hn : 0 < n) (hN : 0 < Fintype.card α)
    (hmean : ∀ i : Fin 2, uniformExpectation (X i) = μ i)
    (hb : ∀ i : Fin 2, ∀ x : α, |X i x| ≤ 1) (hc : 0 < c) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        ∃ i : Fin 2, c ≤ |(∑ t : Fin n, X i (w t)) / n - μ i|))
      ≤ 4 * Real.exp (-(n : ℝ) * c ^ 2 / 8) := by
  have h := good_event_prob X μ n hn hN hmean hb hc
  calc
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        ∃ i : Fin 2, c ≤ |(∑ t : Fin n, X i (w t)) / n - μ i|))
        ≤ ∑ _i : Fin 2, 2 * Real.exp (-(n : ℝ) * c ^ 2 / 8) := h
    _ = 4 * Real.exp (-(n : ℝ) * c ^ 2 / 8) := by
          -- `sum_const` 产出 `nsmul`（`2 • _`），显式转成乘法避免 `norm_num` 的
          -- nsmul 归一化差异（STYLE 建议显式给 `nsmul_eq_mul`）。
          -- ⚠ **G2 修复**：求和后是 `2 * (2 * exp …) = 4 * exp …`，
          -- `norm_num` **不做环上重排**（报 unsolved goals）⟹ 补 `ring`。
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-! ## 定理 6：文献确定性界在 `T = 1` 的**算术事实**（**非**机器验证反例）

文献中常见的 UCB1 陈述是「次优臂 `i` 的拉次数 `N i(T) ≤ 8 ln T / Δ i² + 常数`」。
该陈述作为**确定性**命题在 `T = 1` 时失效：右端 `8 · ln 1 / Δ² = 0`，
但臂 `i` 完全可能在 `t = 1` 被拉一次（此时尚无样本，算法可任选）。

⚠ **诚实标注（本项目纪律要求）**：下面两条**只是算式**，
**本文件没有形式化任何具体算法轨迹**（无策略、无 `N i` 的算法语义、无 `T`
的递推），故**它们不是机器验证的反例**——反例论证本身是**非形式的**。
本文件只固定论证所依赖的关键算式。正确的可证形式是
「好事件下不被拉」（定理 2/3）与「组合上界」（定理 7）。 -/

/-- **关键算式**：`T = 1` 时文献常数界给出的上界恰为 `0`
（因 `Real.log 1 = 0`），故任何「确定性 ≤」形式的界都无法容纳
「`t = 1` 时刻拉一次」这一（非形式论证中的）合法轨迹。 -/
theorem ucb_deterministic_bound_arithmetic (Delta : ℝ) :
    8 * Real.log 1 / Delta ^ 2 = 0 := by
  simp

/-- **算式的存在形式**：文献界在 `T = 1` 时为 `0`，而「拉一次」对应 `1 > 0`。
**仍是算术陈述**，不含算法语义（见本节的诚实标注）。 -/
theorem ucb_deterministic_bound_counterexample :
    ∃ (bound : ℝ) (pulls : ℕ), bound = 8 * Real.log 1 / (1 / 2 : ℝ) ^ 2 ∧ pulls = 1 ∧ bound < (pulls : ℝ) := by
  refine ⟨0, 1, ?_, rfl, by norm_num⟩
  simp

/-! ## 定理 7：悔的组合上界（逐臂控制）

**诚实降级（重要）**：本文件**不证**文献中形如
`regret ≤ (好事件贡献) + 2 · P(坏事件) · T` 的**期望悔分解**——
那需要条件期望，而 mathlib 4.14 的条件期望依赖测度论框架，
与本文件的有限计数设定不符（登记为**未做**）。
本文件只证**纯组合**的部分：若逐臂贡献被 `r i` 控制，则悔 ≤ `∑ i, r i`。
这是 `Finset.sum_le_sum` 的直接应用，作为「好事件 → 悔界」的接口保留；
调用方负责提供 `r i`（例如由定理 3 给出好事件下 `N i = 0`）。 -/

theorem expected_regret_decomposition {g : Fin K → ℝ} {N : Fin K → ℕ}
    {r : Fin K → ℝ}
    (hgood : ∀ i : Fin K, g i * (N i : ℝ) ≤ r i) :
    regret g N ≤ ∑ i : Fin K, r i := by
  unfold regret
  exact Finset.sum_le_sum (fun i _ => hgood i)

/-- 定理 7 的**最坏情形推论**：若所有臂的拉次数被 `T` 控制且间隙 ≤ 1，
则悔 ≤ `T`（平凡但正确的界，用于说明「无概率输入时的确定性退化」）。 -/
theorem regret_le_total_pulls {g : Fin K → ℝ} {N : Fin K → ℕ} {T : ℕ}
    (hgap : ∀ i : Fin K, g i ≤ 1)
    (hN : ∑ i : Fin K, N i ≤ T) :
    regret g N ≤ T := by
  unfold regret
  calc
    ∑ i : Fin K, g i * (N i : ℝ) ≤ ∑ i : Fin K, 1 * (N i : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hgap i) (Nat.cast_nonneg _))
    _ = ∑ i : Fin K, (N i : ℝ) := by simp
    _ = ((∑ i : Fin K, N i : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ T := by exact_mod_cast hN

end Lattice
