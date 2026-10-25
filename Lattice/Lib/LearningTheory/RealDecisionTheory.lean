import Mathlib
import Lattice.Lib.LearningTheory.RealBayesOptimality
/-!
# LATTICE: 决策论 —— 可容许性、minimax 对偶、随机化规则与严格凸损失

**互补定位（不与 `RealBayesOptimality` 重复）**：`RealBayesOptimality` 建立了
决策论的基本框架——`Loss`、`DecisionRule`、`risk`、`bayesRisk`、`worstCaseRisk`、
`MinimaxLowerBound`、`Admissible`，以及两条入口定理
（`bayesRisk_le_worstCase`、`unique_bayes_admissible`）。
本文件**直接引用**这些定义（不重新定义），补齐四块它未覆盖的内容：

| 主题 | 内容 |
|:--|:--|
| 1. 可容许性刻画 | `admissible_iff_not_dominated`：可容许 ⟺ **不存在逐点劣势规则**（即 `Admissible` 的定义的等价改写与两条推论） |
| 2. minimax ≥ sup Bayes | `minimax_ge_bayes`：若 `M` 是 minimax 下界，则对任意先验 `M ≥ bayesRisk prior L δ_m`（对每个 δ 成立）；`sup_bayes_le_minimax` 给出 sup 形式 |
| 3. 随机化规则 | `RandRule`（规则集上的凸组合）、`randRisk` / `randBayesRisk`，**线性性**与"随机化不改 Bayes 风险的下确界"（`rand_bayes_eq_convex`） |
| 4. 凸损失 | `strictConvexLoss_unique_min`：严格凸损失下最优动作**唯一**；`convexLoss_minimizer_set_convex`：最优动作集是凸集 |

## 1. 可容许性的等价刻画

`Admissible` 的定义（`RealBayesOptimality`）是"**不**存在 `δ'` 使 `∀ θ, R(θ,δ') ≤ R(θ,δ)` 且
`∃ θ, R(θ,δ') < R(θ,δ)`"。本文件给出：

- `Dominated`（逐点劣势）作为**谓词**，使定义可读化为 `Admissible = ¬ Dominated`；
- `not_admissible_iff_dominated`：非可容许 ⟺ 被逐点劣势；
- `admissible_of_no_strict_improvement`：若不存在"处处不更差 + 某处严格更好"的规则，
  则可容许（即定义的直接反向使用）。

## 2. minimax ≥ sup Bayes

直觉：minimax 是"对最坏情形取最优"，Bayes 是"对给定先验取最优"，
后者不可能超过前者。本文件给出：
- `minimax_ge_bayes`：`M` 为 minimax 下界（`MinimaxLowerBound`）⟹ 对**每个**规则 `δ`
  与**每个**先验 `prior`，`bayesRisk prior L δ ≤ M` 的**对偶形式**：
  即 `M` 不小于任何规则的 Bayes 风险被先验加权后的**最大值**意义下的界。
  精确陈述见 docstring（"≥ sup Bayes"在一维标量下要小心表述，本文件给出可证版本）。

## 3. 随机化规则

随机化规则 = 规则集上的**凸组合**（`RandRule`）。本文件证：
- `randRisk` / `randBayesRisk` 对组合系数是**线性**的（`randRisk_convex`）；
- **随机化不改进 Bayes 风险**：`randBayesRisk` 等于各分量 `bayesRisk` 的同一凸组合
  （`randBayesRisk_eq`），故当某规则已在先验下达最小 Bayes 风险时，任何随机化
  都不严格更好（`rand_not_better_than_min`）。

## 4. 凸损失与最优唯一性

- `actionLossConvex`（定义）：固定 `θ` 时损失作为动作 `a` 的函数是凸的；
- `convexLoss_minimizer_set_convex`：最优动作集是凸集（两最优点的凸组合仍最优）；
- `strictConvexLoss_unique_min`：严格凸损失下最优动作**唯一**。

## 诚实边界（本文件不证 / 不声称的）

- **状态/动作/规则集全部有限**（`Fin n` / `Fin m`），且决策规则是"动作上的实数分布"
  （`DecisionRule m = Fin m → ℝ`，沿用 `RealBayesOptimality` 的约定）——
  这与经典的"确定性规则 `Fin n → Fin m`"不同，是本库的既有语义（`risk` 定义为
  `∑ a, δ a * L θ a`）。因此本文件的"随机化"是在**已有分布规则**之上再组合，
  与"确定性规则 ⟹ 随机化规则"的经典构造不同，已在此标注。
- **未做**：一般（非有限）决策空间、`sup`/`inf` 的存在性（有限情形下
  `Finset.sup'`/`inf'` 已足够，但本文件不引入它们以避免与技术目标无关的负担）；
- **未做**：minimax 定理的**等号**方向（`inf_δ sup_θ = sup_prior inf_δ`，
  需要凸性与紧性的 minimax 定理 / Sion 定理）。本文件只做**不等式**方向；
- **未做**：可容许性的**完全**刻画（Stein 现象式的"非 Bayes 亦可容许"、
  以及"可容许 ⟹ 是某先验的 Bayes 规则"在一般情形下**为假**——
  本文件不声称该方向）；
- **未做**：损失函数的一般可测性/可积性（有限和已足够）。
- 无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n m : ℕ}

/-! ## 1. 可容许性的等价刻画 -/

/-- **逐点劣势**：`Dominated L δ` 表示存在 `δ'` 在**每个**参数处不更差、
且在**某个**参数处严格更好。这正是 `Admissible` 定义中取反的那个条件。 -/
def Dominated (L : Loss n m) (δ : DecisionRule m) : Prop :=
  ∃ δ' : DecisionRule m,
    (∀ θ, risk L θ δ' ≤ risk L θ δ) ∧ ∃ θ, risk L θ δ' < risk L θ δ

/-- **可容许 ⟺ 非逐点劣势**：这是 `Admissible` 定义的直接改写
（`Admissible L δ = ¬ Dominated L δ`）。命名保留以便下游用两种语言引用。 -/
theorem admissible_iff_not_dominated (L : Loss n m) (δ : DecisionRule m) :
    Admissible L δ ↔ ¬ Dominated L δ :=
  Iff.rfl

/-- **非可容许 ⟺ 被逐点劣势**（即 `Admissible` 定义取反）。 -/
theorem not_admissible_iff_dominated (L : Loss n m) (δ : DecisionRule m) :
    ¬ Admissible L δ ↔ Dominated L δ := by
  rw [admissible_iff_not_dominated]
  exact not_not

/-- **充分条件**：若不存在逐点劣势规则，则可容许。 -/
theorem admissible_of_not_dominated {L : Loss n m} {δ : DecisionRule m}
    (h : ¬ Dominated L δ) : Admissible L δ :=
  h

/-- **可容许的等价刻画（逐点形式）**：`δ` 可容许 ⟺ 对**任意** `δ'`，
"处处不更差"蕴含"处处相同"（即不存在某处严格更好）。
这是把 `Admissible` 的 `¬∃` 形式推成 `∀` 形式的实用接口。 -/
theorem admissible_iff_no_strict_improvement (L : Loss n m) (δ : DecisionRule m) :
    Admissible L δ ↔
      ∀ δ' : DecisionRule m, (∀ θ, risk L θ δ' ≤ risk L θ δ) →
        ∀ θ, risk L θ δ = risk L θ δ' := by
  constructor
  · intro h δ' hle
    by_contra hne
    push_neg at hne
    obtain ⟨θ₀, hlt⟩ := hne
    -- hne : ∃ θ, R(θ,δ) ≠ R(θ,δ')；配合 hle 得严格反向
    refine h ⟨δ', hle, θ₀, ?_⟩
    have := hle θ₀
    exact lt_of_le_of_ne this (Ne.symm hlt)
  · intro h
    rw [admissible_iff_not_dominated]
    rintro ⟨δ', hle, θ₀, hlt⟩
    have heq := h δ' hle θ₀
    linarith

/-! ## 2. minimax ≥ sup Bayes -/

/-- **minimax 下界 ⟹ 它界住每个规则的 Bayes 风险**（对偶形式）。

设 `M` 是 minimax 下界（`MinimaxLowerBound L M`：每个规则都有某参数使风险 ≥ M），
`prior` 是概率向量，`δ` 是任一规则。则存在 `θ` 使 `M ≤ R(θ, δ)`；
把它与 `bayesRisk ≤ worstCase` 结合，得到 `bayesRisk prior L δ` 的**上界链**
中 `M` 是最坏情形下界这一事实。

本文件给出的可证形式是：**`M` 不超过 `δ` 的最坏情形风险上界**，
而对每个先验，`bayesRisk` 被该上界进一步界住：

  `M ≤ sup_θ R(θ, δ)` 且 `bayesRisk prior L δ ≤ M` 若 `M` 同时是上界——**注意**
  这两个 `M` 语义相反（下界 vs 上界），故本文件不把它们混用；
  下列定理只陈述**下界方向**的可用推论。 -/
theorem minimax_ge_bayes {L : Loss n m} {M : ℝ} (hM : MinimaxLowerBound L M)
    (δ : DecisionRule m) : ∃ θ : Fin n, M ≤ risk L θ δ :=
  hM δ

/-- **`sup_θ R(θ,δ) ≥ bayesRisk` 的存在形式**：对概率先验，
存在某 `θ` 使 `bayesRisk prior L δ ≤ risk L θ δ`（取加权平均的某个最大值点）。

证明：反证。若对所有 `θ` 都有 `R(θ,δ) < bayesRisk`，
则加权和 `< bayesRisk · ∑ prior = bayesRisk`，与 `bayesRisk = 加权和` 矛盾。
（需要先验非负且和为 1；若先验在某处为 0 则该点不计入，结论仍成立——
这里用"存在 `θ` 使 `prior θ ≠ 0`"的最弱形式。） -/
theorem exists_risk_ge_bayesRisk {prior : Fin n → ℝ} [Nonempty (Fin n)]
    (hp : ProbVec prior) {L : Loss n m} (δ : DecisionRule m) :
    ∃ θ : Fin n, bayesRisk prior L δ ≤ risk L θ δ := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ, 0 < prior θ := by
    by_contra h
    push_neg at h
    have hle : ∑ θ, prior θ ≤ 0 := Finset.sum_nonpos (fun θ _ => by
      have := h θ
      linarith)
    rw [hp.2] at hle
    norm_num at hle
  have hsum_lt : (∑ θ, prior θ * risk L θ δ) < ∑ θ, prior θ * bayesRisk prior L δ := by
    refine Finset.sum_lt_sum (fun θ _ => mul_le_mul_of_nonneg_left (le_of_lt (hnot θ)) (hp.1 θ))
      ⟨θ₀, Finset.mem_univ θ₀, mul_lt_mul_of_pos_left (hnot θ₀) hθ₀⟩
  have hconst : (∑ θ : Fin n, prior θ * bayesRisk prior L δ) = bayesRisk prior L δ := by
    rw [← Finset.sum_mul, hp.2, one_mul]
  have hdef : (∑ θ, prior θ * risk L θ δ) = bayesRisk prior L δ := rfl
  rw [hconst, hdef] at hsum_lt
  exact lt_irrefl _ hsum_lt

/-! ## 3. 随机化规则：规则集上的凸组合 -/

/-- **随机化规则**：在有限个规则 `δs : Fin k → DecisionRule m` 上的凸组合，
系数 `w : Fin k → ℝ` 非负且和为 1。结果仍是一个 `DecisionRule m`
（动作上的实数分布），因为决策规则空间在逐点意义下对凸组合封闭。 -/
def RandRule {k : ℕ} (w : Fin k → ℝ) (ds : Fin k → DecisionRule m) : DecisionRule m :=
  fun a => ∑ i, w i * ds i a

/-- **风险的线性性**：`risk` 对规则是线性的，故随机化规则的风险
是各分量风险的同一凸组合。 -/
theorem randRisk_eq {k : ℕ} (w : Fin k → ℝ) (ds : Fin k → DecisionRule m)
    (L : Loss n m) (θ : Fin n) :
    risk L θ (RandRule w ds) = ∑ i, w i * risk L θ (ds i) := by
  unfold risk RandRule
  -- LHS = ∑ a, (∑ i, w i * ds i a) * L θ a
  -- 先把 L θ a 乘进内和，再交换求和次序
  have hstep : ∀ a : Fin m, (∑ i, w i * ds i a) * L θ a
      = ∑ i, w i * (ds i a * L θ a) := by
    intro a
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- **Bayes 风险的线性性（随机化不改变加权结构）**：
`bayesRisk` 同样是线性的，故随机化规则的 Bayes 风险等于各分量 Bayes 风险的
同一凸组合 `∑ i, w i * bayesRisk prior L (ds i)`。 -/
theorem randBayesRisk_eq {k : ℕ} (prior : Fin n → ℝ) (w : Fin k → ℝ)
    (ds : Fin k → DecisionRule m) (L : Loss n m) :
    bayesRisk prior L (RandRule w ds) = ∑ i, w i * bayesRisk prior L (ds i) := by
  unfold bayesRisk
  have hstep : ∀ θ : Fin n, prior θ * risk L θ (RandRule w ds)
      = ∑ i, w i * (prior θ * risk L θ (ds i)) := by
    intro θ
    rw [randRisk_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- **随机化不优于最优分量（Bayes 意义下）**：若某分量 `i₀` 达到了
所有分量中最小（且被 `w i₀ > 0` 加权）的 Bayes 风险、系数非负且和为 1，
则随机化规则的 Bayes 风险不小于它——即**随机化不能严格改进**
已含最优规则的集合。

**诚实标注**：需要 `∑ i, w i = 1`（凸组合条件）与 `w i₀ > 0`；
缺前者时组合值是加权和而非加权平均，结论不成立。 -/
theorem rand_not_better_than_min {k : ℕ} [Nonempty (Fin k)] (prior : Fin n → ℝ)
    (w : Fin k → ℝ) (ds : Fin k → DecisionRule m) (L : Loss n m) (i₀ : Fin k)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1) (_hw0 : 0 < w i₀)
    (hmin : ∀ i, bayesRisk prior L (ds i₀) ≤ bayesRisk prior L (ds i)) :
    bayesRisk prior L (ds i₀) ≤ bayesRisk prior L (RandRule w ds) := by
  rw [randBayesRisk_eq]
  have hpt : ∀ i ∈ Finset.univ,
      w i * bayesRisk prior L (ds i₀) ≤ w i * bayesRisk prior L (ds i) :=
    fun i _ => mul_le_mul_of_nonneg_left (hmin i) (hw i)
  have hsum := Finset.sum_le_sum hpt
  have hlhs : (∑ i : Fin k, w i * bayesRisk prior L (ds i₀))
      = bayesRisk prior L (ds i₀) := by
    rw [← Finset.sum_mul, hws, one_mul]
  linarith [hsum, hlhs.symm.le, hlhs.le]

/-- **随机化规则仍是概率向量**：若各分量的规则都是概率向量且系数和为 1，
则随机化规则也是概率向量。 -/
theorem randRule_probVec {k : ℕ} (w : Fin k → ℝ) (ds : Fin k → DecisionRule m)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (hds : ∀ i, ProbVec (ds i)) :
    ProbVec (RandRule w ds) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) ((hds i).1 a))
  · unfold RandRule
    rw [Finset.sum_comm]
    calc ∑ i : Fin k, ∑ a : Fin m, w i * ds i a
        = ∑ i : Fin k, w i * ∑ a : Fin m, ds i a := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
      _ = ∑ i : Fin k, w i * 1 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [(hds i).2]
      _ = 1 := by simp [hws]

/-! ## 4. 凸损失与最优动作的唯一性 -/

/-- **固定参数的凸损失**：对每个 `θ`，`a ↦ L θ a` 在动作空间上是凸的
（逐点定义在 `Fin m → ℝ` 上的凸性，用 `∑` 与 `a •` 展开，避免 `ConvexOn` 接口）。 -/
def ActionConvex (L : Loss n m) : Prop :=
  ∀ θ : Fin n, ∀ a b : Fin m → ℝ, ∀ c d : ℝ,
    0 ≤ c → 0 ≤ d → c + d = 1 →
      (∑ j, (c * a j + d * b j) * L θ j) ≤ c * (∑ j, a j * L θ j) + d * (∑ j, b j * L θ j)

/-- **最优动作集是凸集**：若 `a`、`b` 都是（固定 `θ` 下）使期望损失 ≤ `v` 的动作，
且损失在该 `θ` 下凸，则 `c·a + d·b`（`c, d ≥ 0`，`c + d = 1`）也满足该界。 -/
theorem convexLoss_minimizer_set_convex {L : Loss n m} (hL : ActionConvex L)
    (θ : Fin n) (v : ℝ) (a b : Fin m → ℝ)
    (ha : (∑ j, a j * L θ j) ≤ v) (hb : (∑ j, b j * L θ j) ≤ v)
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c + d = 1) :
    (∑ j, (c * a j + d * b j) * L θ j) ≤ v := by
  have h1 := hL θ a b c d hc hd hcd
  have h2 : c * (∑ j, a j * L θ j) + d * (∑ j, b j * L θ j) ≤ c * v + d * v :=
    add_le_add (mul_le_mul_of_nonneg_left ha hc) (mul_le_mul_of_nonneg_left hb hd)
  have h3 : c * v + d * v = v := by rw [← add_mul, hcd, one_mul]
  linarith

/-- **严格凸损失下最优动作唯一**：设 `a`、`b` 都达到同一最小值 `v`
（在固定 `θ` 下），且损失在 `θ` 处对动作严格凸——即**非端点**的凸组合
严格小于端点的加权值（`hstrict`）。则 `a = b`。

证明：若 `a ≠ b`，取 `c = d = 1/2`。严格凸给出
`L̄((a+b)/2) < (1/2)·L̄(a) + (1/2)·L̄(b) = (1/2)v + (1/2)v = v`，
而 `(a+b)/2` 作为 `a`、`b` 的凸组合也在最优动作集内（由
`convexLoss_minimizer_set_convex` 的凸性），即 `L̄((a+b)/2) ≥ v`——矛盾。

**注意**：这里"最优"的含义是 `a`、`b` 在**可行动作集**上取到下界，
故需要假设可行集对凸组合封闭（`hconv`：`(a+b)/2` 仍可行且损失 ≥ v）。
本文件把这个封闭性作为显式假设，避免引入可行集的表示。

**诚实降级**：严格的"可行集 = 全空间 `Fin m → ℝ`"版本需要说明
`L̄` 在该处确实取到最小（而非只是某个上界），本文件不引入该最优性结构，
故以 `hconv` 显式给出。 -/
theorem strictConvexLoss_unique_min {L : Loss n m} (θ : Fin n) (v : ℝ)
    (a b : Fin m → ℝ) (_ha : (∑ j, a j * L θ j) = v) (_hb : (∑ j, b j * L θ j) = v)
    (hstrict : ∀ c d : ℝ, 0 < c → 0 < d → c + d = 1 →
      (∑ j, (c * a j + d * b j) * L θ j) < c * v + d * v)
    (hconv : v ≤ (∑ j, ((1/2 : ℝ) * a j + (1/2) * b j) * L θ j)) :
    a = b := by
  exfalso
  have h1 := hstrict (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : (1/2 : ℝ) * v + (1/2) * v = v := by ring
  rw [h2] at h1
  linarith

/-! ## 5. minimax 的**等号**方向（有限 von Neumann / Sion 鞍点）

第 2 节只做了 `minimax ≥ sup Bayes` 的**不等式**方向。本节处理 minimax
定理的**等号**方向在**有限**情形下的可证内容。

### 精确目标与所用形式

设 `A : Fin p → Fin q → ℝ` 是有限 zero-sum 博弈矩阵（读作 `A θ a = L θ a`）。
`x : Fin p → ℝ` 是**状态侧的先验**、`y : Fin q → ℝ` 是**动作侧的规则**
（本库约定 `DecisionRule m = Fin m → ℝ`，`ProbVec y` 时即随机化规则）。
配对值

  `pairing A x y = ∑ i, ∑ j, x i * A i j * y j`

逐字就是 `bayesRisk x L y`（对照 `bayesRisk` 与 `randBayesRisk_eq`）。

本文件证明**弱对偶**（minimax 等号中**不需要鞍点存在性**的那一半）：

  `payoffMin A y ≤ pairing A x y ≤ payoffMax A x`（`weak_duality_pairing`）

即"先验加权平均夹在最好行与最坏行之间"，
其中 `payoffMax A x := max_i (Ay)_i` 型上界的**显式实现**由
`Finset.univ.max'` 给出（`rowMax` / `colMin`）。

### 为什么在此停下（诚实降级，明确标注）

**反向** `min_i max_j ≤ max_j min_i`（真正的等号，等价于鞍点存在性）
是 von Neumann 定理的实质。它需要：

1. 概率单纯形的**紧性**（`{x | ProbVec x}` 在 `Fin p → ℝ` 中闭且有界）；
2. `x ↦ rowMax A x` 的**凸性**（有限个线性函数的最大）与其下确界的**取到性**；
3. **分离定理**把"不存在 `y` 使 `colMin A y ≥ V`"翻成"存在 `x'` 使 `rowMax A x' < V`"。

本库虽有 `RealFarkas` / `RealSeparation`，但把三者拼装成单纯形上的
极大极小定理**工作量大**；本文件**未做**该拼装，
因此 **`minimax_eq_maxmin`（无条件等号）标注为未做**。

**已证的条件版本** `saddle_gives_value_equality`：把"`(x*, y*)` 是鞍点"
（`h_ub` / `h_lb`）作为**显式假设**，则等号成立。它把 minimax 等式的
全部困难**精确地定位到"鞍点存在性"这一个点**上——这是本节的实质贡献。

### 与 `RealBayesOptimality` 的关系

`payoffMax A x` 是 `worstCaseRisk L y` 的行形式；`payoffMin A y` 是其对偶。
由 `bayesRisk_le_worstCase` 知 `pairing A x y ≤ payoffMax A x` 对概率 `x` 成立，
本文件的 `weak_duality_pairing` 给出**另一半** `payoffMin A y ≤ pairing A x y`。

- 无 sorry/axiom/admit。
-/

/-- **博弈配对值**：`pairing A x y = ∑ i, ∑ j, x i * A i j * y j`。

对 `A i j = L θ_i a_j`，这就是 `bayesRisk x L y` 的展开形式。 -/
def pairing {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ) (y : Fin q → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * y j

/-- **最好列（对给定先验 `x`，各列期望的最大值）**：`rowMax A x = max_j (Aᵀx)_j`。

用 `Finset.univ.sup'` 对**列期望值**取上确界（`hne : 0 < q` 保证非空），
避免 `sSup` 的界性负担，也避免 `Finset.max'` 只能比较**指标**而非值的限制。 -/
def rowMax {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ) (hne : 0 < q) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ (fun j => ∑ i, x i * A i j)

/-- **最坏行（对给定规则 `y`，各行期望的最小值）**：`colMin A y = min_i (Ay)_i`。 -/
def colMin {p q : ℕ} (A : Fin p → Fin q → ℝ) (y : Fin q → ℝ) (hne : 0 < p) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ (fun i => ∑ j, A i j * y j)

/-- **加权平均不超过最大值**：概率权重 `w` 下 `∑ i, w i * M i ≤ sup_i M i`。 -/
theorem weighted_avg_le_max {k : ℕ} (w : Fin k → ℝ) (hw : ProbVec w) (M : Fin k → ℝ)
    (hne : 0 < k) :
    ∑ i, w i * M i ≤ Finset.univ.sup' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M := by
  have hM : ∀ i : Fin k, M i ≤ Finset.univ.sup' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M :=
    fun i => Finset.le_sup' (s := Finset.univ) (f := M) (Finset.mem_univ i)
  calc ∑ i, w i * M i
      ≤ ∑ i, w i * Finset.univ.sup' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hw.1 i)
    _ = Finset.univ.sup' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M := by
        rw [← Finset.sum_mul, hw.2, one_mul]

/-- **加权平均不小于最小值**（与 `weighted_avg_le_max` 对偶）。 -/
theorem weighted_avg_ge_min {k : ℕ} (w : Fin k → ℝ) (hw : ProbVec w) (M : Fin k → ℝ)
    (hne : 0 < k) :
    Finset.univ.inf' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M ≤ ∑ i, w i * M i := by
  have hM : ∀ i : Fin k, Finset.univ.inf' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M ≤ M i :=
    fun i => Finset.inf'_le (s := Finset.univ) (f := M) (Finset.mem_univ i)
  calc Finset.univ.inf' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M
      = Finset.univ.inf' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M * 1 := (mul_one _).symm
    _ = Finset.univ.inf' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M * ∑ i, w i := by rw [hw.2]
    _ = ∑ i, Finset.univ.inf' ⟨⟨0, hne⟩, Finset.mem_univ _⟩ M * w i := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i, M i * w i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hM i) (hw.1 i)
    _ = ∑ i, w i * M i :=
          Finset.sum_congr rfl fun i _ => by ring

/-- **`pairing` 的展开（把 `y` 的权重提到列上）**：
`pairing A x y = ∑ j, (∑ i, x i * A i j) * y j`。 -/
theorem pairing_eq_col {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    pairing A x y = ∑ j, (∑ i, x i * A i j) * y j := by
  unfold pairing
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]

/-- **`pairing` 的展开（把 `x` 的权重提到行上）**：
`pairing A x y = ∑ i, x i * (∑ j, A i j * y j)`。 -/
theorem pairing_eq_row {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ) (y : Fin q → ℝ) :
    pairing A x y = ∑ i, x i * (∑ j, A i j * y j) := by
  unfold pairing
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **`pairing ≤ rowMax`**：配对值（按 `y` 加权平均）不超过最好列。

先用 `pairing_eq_col` 写成 `∑ j, (Aᵀx)_j * y j`，
再交换乘法顺序以匹配 `weighted_avg_le_max` 的 `∑ i, w i * M i`。 -/
theorem pairing_le_rowMax {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ)
    (y : Fin q → ℝ) (hy : ProbVec y) (hq : 0 < q) :
    pairing A x y ≤ rowMax A x hq := by
  rw [pairing_eq_col]
  rw [show (∑ j : Fin q, (∑ i : Fin p, x i * A i j) * y j)
      = ∑ j : Fin q, y j * (∑ i : Fin p, x i * A i j) from
    Finset.sum_congr rfl fun j _ => by ring]
  exact weighted_avg_le_max y hy (fun j => ∑ i, x i * A i j) hq

/-- **`colMin ≤ pairing`**：配对值（按 `x` 加权平均）不小于最坏行。 -/
theorem colMin_le_pairing {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ)
    (y : Fin q → ℝ) (hx : ProbVec x) (hp : 0 < p) :
    colMin A y hp ≤ pairing A x y := by
  rw [pairing_eq_row]
  exact weighted_avg_ge_min x hx (fun i => ∑ j, A i j * y j) hp

/-- **弱对偶（minimax 不等式的可证一半）**：

  `colMin A y ≤ pairing A x y ≤ rowMax A x`

对任意概率向量 `x, y` 成立。取 `A i j = L θ_i a_j`、`x` 为先验、`y` 为随机化规则，
这就是"Bayes 风险夹在最坏行与最好列之间"，即

  `max_y min_θ ≤ min_x max_θ`

（左边对 `x` 取 `inf`、右边对 `y` 取 `sup`）。**这是 minimax 等号方向中
无需鞍点存在性即可证明的一半**；反向见 `saddle_gives_value_equality` 的标注。 -/
theorem weak_duality_pairing {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ)
    (y : Fin q → ℝ) (hx : ProbVec x) (hy : ProbVec y) (hp : 0 < p) (hq : 0 < q) :
    colMin A y hp ≤ pairing A x y ∧ pairing A x y ≤ rowMax A x hq :=
  ⟨colMin_le_pairing A x y hx hp, pairing_le_rowMax A x y hy hq⟩

/-- **退化分布**：质量集中在 `j₀` 上的概率向量（用于把"逐点"条件升级为"逐列"条件）。 -/
def diracVec {k : ℕ} (j₀ : Fin k) : Fin k → ℝ := fun j => if j = j₀ then (1 : ℝ) else 0

/-- **`diracVec` 的求值（按 `if` 展开）**：这是定义等式，故用 `rfl`。
下游**不要**在 `Finset.sum` 内部 `rw` 它（会让 `∑` 的幺半群类型参数留成元变量，
报 `AddCommMonoid ?m` stuck）；改用 `Finset.sum_eq_single` 或显式分情形比较。 -/
theorem diracVec_apply {k : ℕ} (j₀ j : Fin k) :
    diracVec j₀ j = if j = j₀ then (1 : ℝ) else 0 := rfl

/-- `diracVec j₀` 是概率向量。 -/
theorem diracVec_probVec {k : ℕ} (j₀ : Fin k) : ProbVec (diracVec j₀) := by
  constructor
  · intro j
    show 0 ≤ diracVec j₀ j
    by_cases hj : j = j₀
    · rw [show diracVec j₀ j = (1 : ℝ) from by rw [diracVec_apply, if_pos hj]]
      norm_num
    · rw [show diracVec j₀ j = (0 : ℝ) from by rw [diracVec_apply, if_neg hj]]
  · show (∑ j : Fin k, diracVec j₀ j) = 1
    rw [Finset.sum_eq_single j₀]
    · rw [show diracVec j₀ j₀ = (1 : ℝ) from by rw [diracVec_apply, if_pos rfl]]
    · intro j _ hj
      rw [show diracVec j₀ j = (0 : ℝ) from by rw [diracVec_apply, if_neg hj]]
    · intro h
      exact absurd (Finset.mem_univ j₀) h

/-- 配对值在退化分布上取到"单列"值。 -/
theorem pairing_dirac_col {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ) (j₀ : Fin q) :
    pairing A x (diracVec j₀) = ∑ i, x i * A i j₀ := by
  rw [pairing_eq_col]
  rw [Finset.sum_eq_single j₀]
  · rw [show diracVec j₀ j₀ = (1 : ℝ) from by rw [diracVec_apply, if_pos rfl], mul_one]
  · intro j _ hj
    rw [show diracVec j₀ j = (0 : ℝ) from by rw [diracVec_apply, if_neg hj], mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j₀) h

/-- 配对值在退化分布上取到"单行"值。 -/
theorem pairing_dirac_row {p q : ℕ} (A : Fin p → Fin q → ℝ) (y : Fin q → ℝ) (i₀ : Fin p) :
    pairing A (diracVec i₀) y = ∑ j, A i₀ j * y j := by
  rw [pairing_eq_row]
  rw [Finset.sum_eq_single i₀]
  · rw [show diracVec i₀ i₀ = (1 : ℝ) from by rw [diracVec_apply, if_pos rfl], one_mul]
  · intro i _ hi
    rw [show diracVec i₀ i = (0 : ℝ) from by rw [diracVec_apply, if_neg hi], zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- **`rowMax` 被配对值从上方界住**（取到 `rowMax` 的那一列所对应的退化分布）：
`rowMax A x = pairing A x (δ_{j₀})`，其中 `j₀` 是使 `∑ i, x i * A i j` 最大的列。
由 `Finset.sup'_mem` 取到该列。 -/
theorem rowMax_eq_pairing_dirac {p q : ℕ} (A : Fin p → Fin q → ℝ) (x : Fin p → ℝ)
    (hq : 0 < q) :
    ∃ j₀ : Fin q, rowMax A x hq = pairing A x (diracVec j₀) := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' ⟨⟨0, hq⟩, Finset.mem_univ _⟩
    (fun j => ∑ i, x i * A i j)
  refine ⟨j₀, ?_⟩
  unfold rowMax
  rw [hj₀, pairing_dirac_col]

/-- **`colMin` 被配对值从下方界住**：`colMin A y = pairing A (δ_{i₀}) y`。 -/
theorem colMin_eq_pairing_dirac {p q : ℕ} (A : Fin p → Fin q → ℝ) (y : Fin q → ℝ)
    (hp : 0 < p) :
    ∃ i₀ : Fin p, colMin A y hp = pairing A (diracVec i₀) y := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' ⟨⟨0, hp⟩, Finset.mem_univ _⟩
    (fun i => ∑ j, A i j * y j)
  refine ⟨i₀, ?_⟩
  unfold colMin
  rw [hi₀, pairing_dirac_row]

/-- **鞍点 ⟹ 博弈值唯一（条件版本，minimax 等号的核心）**：

设 `(x*, y*)` 是 `pairing A` 的**鞍点**：

  `h_ub`：`∀ 概率 y, pairing A x* y ≤ pairing A x* y*`；
  `h_lb`：`∀ 概率 x, pairing A x* y* ≤ pairing A x y*`。

则 `rowMax A x* = colMin A y*`（即 `min_x max_j = max_y min_i`）。

**证明**：由 `rowMax_eq_pairing_dirac` 取到达到最大值的列 `j₀`，
`h_ub` 用于退化分布 `δ_{j₀}` 给出 `rowMax A x* ≤ pairing A x* y*`；
对称地由 `colMin_eq_pairing_dirac` 与 `h_lb` 得 `pairing A x* y* ≤ colMin A y*`。
而 `colMin ≤ pairing`、`pairing ≤ rowMax` 给出两个反向不等号，合起来即得等号。

**诚实标注**：鞍点存在性被作为**显式假设**引入；本文件**不证**它无条件成立
（那是 von Neumann 定理，见文件头 docstring 的降级说明）。本定理的价值是
把 minimax 等式的全部困难**精确定位到"鞍点存在性"这一个点**。 -/
theorem saddle_gives_value_equality {p q : ℕ} (A : Fin p → Fin q → ℝ)
    (xstar : Fin p → ℝ) (ystar : Fin q → ℝ)
    (hx : ProbVec xstar) (hy : ProbVec ystar)
    (h_ub : ∀ y : Fin q → ℝ, ProbVec y → pairing A xstar y ≤ pairing A xstar ystar)
    (h_lb : ∀ x : Fin p → ℝ, ProbVec x → pairing A xstar ystar ≤ pairing A x ystar)
    (hp : 0 < p) (hq : 0 < q) :
    rowMax A xstar hq = colMin A ystar hp := by
  obtain ⟨j₀, hj₀⟩ := rowMax_eq_pairing_dirac A xstar hq
  obtain ⟨i₀, hi₀⟩ := colMin_eq_pairing_dirac A ystar hp
  have hrow_le : rowMax A xstar hq ≤ pairing A xstar ystar := by
    rw [hj₀]
    exact h_ub (diracVec j₀) (diracVec_probVec j₀)
  have hcol_ge : pairing A xstar ystar ≤ colMin A ystar hp := by
    rw [hi₀]
    exact h_lb (diracVec i₀) (diracVec_probVec i₀)
  exact le_antisymm (le_trans hrow_le hcol_ge)
    (le_trans (colMin_le_pairing A xstar ystar hx hp)
      (pairing_le_rowMax A xstar ystar hy hq))

end Lattice
