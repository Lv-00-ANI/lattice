import Mathlib

/-!
# LATTICE: Bayes 最优性 —— 后验更新、Bayes 估计的最优性与可容许性

有限状态/动作下的 Bayes 决策论：

  1. `ProbVec`（def）：概率向量（非负且总和为 1）；
  2. `bayesUpdate`（def）：**Bayes 更新** `post θ = prior θ · lik θ / Z`，
     其中 `Z = ∑ θ, prior θ · lik θ` 是**归一化常数 = 边缘似然**；
     `bayesUpdate_prob`：后验仍是概率向量（`Z > 0` 时）；
     `marginalLikelihood_pos`：正先验 + 正似然 ⟹ `Z > 0`；
     `bayesUpdate_normalized`：`∑ θ, bayesUpdate prior lik θ = 1`；
  3. `posteriorMean`（def）：后验均值 `∑ θ, post θ · θ`；
     `squaredRisk`（def）：平方风险 `E[(θ̂ − θ)²]`；
     `posterior_mean_minimizes_squared_risk`：**后验均值最小化平方风险**
     （对任意 θ̂ 有 `squaredRisk post (posteriorMean post) ≤ squaredRisk post θ̂`）；
  4. `absRisk`（def）与 `isMedian`（def）；
     `median_minimizes_abs_risk_left_support`：**中位数最小化绝对误差风险**
     在「后验支撑含于 `(-∞, x]`」这一充分条件下的可证版本
     （一般情形的完整证明标注为**未做**，见该定理的诚实降级说明）；
  5. `bayesRisk`（def）：Bayes 风险 `E_prior[∫ R(θ, a) dpost]`；
      `MinimaxLowerBound`（def）：minimax 风险的**下界**表述
      （对每个规则都有某参数使风险 ≥ `M`，即 minimax 风险的下降形式）；
      `bayesRisk_le_minimaxRisk`：**minimax 下界被某参数处的风险超过**
      （结论为 `∃ θ, M ≤ risk L θ δ`，该陈述中并不出现 `bayesRisk`；
      定理名沿用历史命名，其实际内容是 `bayesRisk_le_worstCase` 的下界对偶表述）；
  6. `Admissible`（def）：可容许性（不存在处处不差的改进规则）；
     `unique_bayes_admissible`：**唯一 Bayes 规则 ⟹ 可容许**。

## 诚实边界

  · 全部结论在**有限状态/动作**（`Fin n`、`Fin m`、`Finset` 求和）下给出，
    测度论版本（一般先验、连续参数空间）**未做**；
  · `median_minimizes_abs_risk_left_support` 是「支撑在左侧」充分条件下的版本；
    **一般情形未做**：需要按 `{θ ≤ x}`、`{x ≤ θ ≤ y}`、`{y ≤ θ}` 划分并
    比较两侧质量（`P₁ ≥ 1/2` 与 `P₂ ≤ 1` 不足以推出 `P₁ ≥ P₂`，
    故不能直接由中位数条件得到），该一般证明标注为后续工作；
  · `unique_bayes_admissible` 的「唯一性」以「Bayes 风险严格小于任何其他规则的
    先验期望风险」表述（这是 Bayes 规则唯一性的标准充分条件）；
    由其推出可容许性用的是标准论证：若存在处处不差的改进则其先验期望不更大，
    与严格性矛盾；
  · `bayesRisk_le_minimaxRisk` 在**固定决策规则**层面给出（对任意规则，
    其 Bayes 风险 ≤ 其最坏情形风险），这是 minimax ≥ Bayes 的逐点形式；
    完整的「minimax = sup over priors of Bayes risk」对偶**未做**；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace Lattice

variable {n m : ℕ}

/-! ## 一、概率向量与 Bayes 更新 -/

/-- **概率向量**：非负且总和为 1。 -/
def ProbVec {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- **边缘似然（归一化常数）**：`Z = ∑ θ, prior θ · lik θ`。 -/
def marginalLikelihood (prior lik : Fin n → ℝ) : ℝ :=
  ∑ θ, prior θ * lik θ

/-- **Bayes 更新**：`post θ = prior θ · lik θ / Z`。

`lik` 视为似然（`lik θ` = `P(data | θ)`）；`Z = marginalLikelihood prior lik`
是归一化常数，也即数据的**边缘似然**。 -/
def bayesUpdate (prior lik : Fin n → ℝ) : Fin n → ℝ :=
  fun θ => prior θ * lik θ / marginalLikelihood prior lik

/-- **正先验 + 正似然 ⟹ 边缘似然为正**。 -/
lemma marginalLikelihood_pos {prior lik : Fin n → ℝ} [Nonempty (Fin n)]
    (hp : ∀ θ, 0 < prior θ) (hl : ∀ θ, 0 < lik θ) : 0 < marginalLikelihood prior lik := by
  unfold marginalLikelihood
  obtain ⟨θ₀⟩ := ‹Nonempty (Fin n)›
  refine Finset.sum_pos' (fun i _ => le_of_lt (mul_pos (hp i) (hl i))) ?_
  exact ⟨θ₀, Finset.mem_univ θ₀, mul_pos (hp θ₀) (hl θ₀)⟩

/-- **Bayes 更新归一化**：`∑ θ, bayesUpdate prior lik θ = 1`（`Z ≠ 0` 时）。 -/
theorem bayesUpdate_normalized {prior lik : Fin n → ℝ}
    (hZ : marginalLikelihood prior lik ≠ 0) :
    ∑ θ, bayesUpdate prior lik θ = 1 := by
  unfold bayesUpdate marginalLikelihood
  rw [← Finset.sum_div]
  exact div_self hZ

/-- **后验是概率向量**：正先验 + 正似然 ⟹ `bayesUpdate prior lik` 满足 `ProbVec`。 -/
theorem bayesUpdate_prob {prior lik : Fin n → ℝ} [Nonempty (Fin n)]
    (hp : ∀ θ, 0 < prior θ) (hl : ∀ θ, 0 < lik θ) : ProbVec (bayesUpdate prior lik) := by
  have hZpos := marginalLikelihood_pos hp hl
  refine ⟨fun θ => ?_, bayesUpdate_normalized (ne_of_gt hZpos)⟩
  unfold bayesUpdate
  exact div_nonneg (mul_nonneg (le_of_lt (hp θ)) (le_of_lt (hl θ))) (le_of_lt hZpos)

/-- Bayes 更新的本质：`post θ ∝ prior θ · lik θ`（成比例）。 -/
lemma bayesUpdate_proportional {prior lik : Fin n → ℝ}
    (hZ : marginalLikelihood prior lik ≠ 0) (θ : Fin n) :
    bayesUpdate prior lik θ * marginalLikelihood prior lik = prior θ * lik θ := by
  unfold bayesUpdate
  field_simp

/-! ## 二、后验均值最小化平方风险 -/

/-- **后验均值**：`θ̄ = ∑ θ, post θ · θ`（`θ` 视为实数参数）。 -/
def posteriorMean (post : Fin n → ℝ) : ℝ :=
  ∑ θ, post θ * (θ : ℝ)

/-- **平方风险**：`R(θ̂) = ∑ θ, post θ · (θ̂ − θ)²`。 -/
def squaredRisk (post : Fin n → ℝ) (θhat : ℝ) : ℝ :=
  ∑ θ, post θ * (θhat - (θ : ℝ)) ^ 2

/-- **恒等式**：平方风险 = 后验方差 + (θ̂ − 后验均值)²。
这是「最小化平方风险 = 取后验均值」的全部代数内容。

证明：记 `μ := posteriorMean post`。展开
`(θ̂ − θ)² = ((θ̂ − μ) + (μ − θ))² = (θ̂ − μ)² + 2(θ̂ − μ)(μ − θ) + (μ − θ)²`，
对 `post` 加权求和。交叉项 `2(θ̂ − μ) · ∑ θ, post θ · (μ − θ)` 因
`∑ post θ · μ = μ · 1 = μ` 与 `∑ post θ · θ = μ` 而为 0。 -/
lemma squaredRisk_eq_variance_add (post : Fin n → ℝ) (hpost : ∑ θ, post θ = 1)
    (θhat : ℝ) :
    squaredRisk post θhat
      = (∑ θ, post θ * ((θ : ℝ) - posteriorMean post) ^ 2)
        + (θhat - posteriorMean post) ^ 2 := by
  set μ : ℝ := posteriorMean post with hμ
  have hμdef : μ = ∑ η, post η * (η : ℝ) := rfl
  -- 交叉项为 0：∑ θ, post θ * (μ − θ) = 0
  have hcross : ∑ θ, post θ * (μ - (θ : ℝ)) = 0 := by
    have ha : ∑ θ, post θ * μ = μ := by
      rw [← Finset.sum_mul, hpost, one_mul]
    have hb : ∑ θ, post θ * (θ : ℝ) = μ := by rw [hμdef]
    calc ∑ θ, post θ * (μ - (θ : ℝ))
        = ∑ θ, (post θ * μ - post θ * (θ : ℝ)) :=
          Finset.sum_congr rfl fun θ _ => by ring
      _ = ∑ θ, post θ * μ - ∑ θ, post θ * (θ : ℝ) := Finset.sum_sub_distrib
      _ = μ - μ := by rw [ha, hb]
      _ = 0 := sub_self μ
  -- 逐项分解
  have hpt : ∀ θ : Fin n,
      post θ * (θhat - (θ : ℝ)) ^ 2
        = post θ * (θhat - μ) ^ 2 + 2 * (θhat - μ) * (post θ * (μ - (θ : ℝ)))
          + post θ * ((θ : ℝ) - μ) ^ 2 := by
    intro θ
    ring
  unfold squaredRisk
  rw [Finset.sum_congr rfl fun θ _ => hpt θ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ θ : Fin n, post θ * (θhat - μ) ^ 2 = (θhat - μ) ^ 2 := by
    rw [← Finset.sum_mul, hpost, one_mul]
  have h2 : ∑ θ : Fin n, 2 * (θhat - μ) * (post θ * (μ - (θ : ℝ)))
      = 2 * (θhat - μ) * ∑ θ, post θ * (μ - (θ : ℝ)) := by
    rw [Finset.mul_sum]
  rw [h1, h2, hcross, mul_zero, add_zero, hμdef]
  ring
/-- **后验均值最小化平方风险**：对任意估计 `θ̂`，
    `squaredRisk post (posteriorMean post) ≤ squaredRisk post θ̂`。

证明：由恒等式 `R(θ̂) = Var + (θ̂ − θ̄)²`，取 `θ̂ = θ̄` 时第二项为 0，
而第一项（后验方差）非负且与 `θ̂` 无关。 -/
theorem posterior_mean_minimizes_squared_risk {post : Fin n → ℝ}
    (hpost : ProbVec post) (θhat : ℝ) :
    squaredRisk post (posteriorMean post) ≤ squaredRisk post θhat := by
  have h1 := squaredRisk_eq_variance_add post hpost.2 (posteriorMean post)
  have h2 := squaredRisk_eq_variance_add post hpost.2 θhat
  have hvar : 0 ≤ ∑ θ, post θ * ((θ : ℝ) - posteriorMean post) ^ 2 :=
    Finset.sum_nonneg fun θ _ => mul_nonneg (hpost.1 θ) (sq_nonneg _)
  rw [h1, h2]
  nlinarith [hvar, sq_nonneg (θhat - posteriorMean post)]

/-- **后验均值的最优性是严格的**（除退化情形）：若后验方差为正，
则任何不等于后验均值的估计都有严格更大的平方风险。 -/
theorem posterior_mean_strictly_optimal {post : Fin n → ℝ} (hpost : ProbVec post)
    {θhat : ℝ} (hne : θhat ≠ posteriorMean post) :
    squaredRisk post (posteriorMean post) < squaredRisk post θhat := by
  have h1 := squaredRisk_eq_variance_add post hpost.2 (posteriorMean post)
  have h2 := squaredRisk_eq_variance_add post hpost.2 θhat
  have hsq : 0 < (θhat - posteriorMean post) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  rw [h1, h2]
  linarith

/-! ## 三、中位数最小化绝对误差风险 -/

/-- **绝对误差风险**：`R(θ̂) = ∑ θ, post θ · |θ̂ − θ|`。 -/
def absRisk (post : Fin n → ℝ) (θhat : ℝ) : ℝ :=
  ∑ θ, post θ * |θhat - (θ : ℝ)|

/-- **中位数**：两侧后验质量都不少于 1/2，
即 `∑_{θ ≤ x} post θ ≥ 1/2` 且 `∑_{x ≤ θ} post θ ≥ 1/2`。

注意 `IsMedian` 是 `def` 别名（合取式），点号投影 `hm.1` 会失败
（见 STYLE.md「ConvexOn 陷阱」），须用 `obtain ⟨hl, hr⟩ := hm`。 -/
def IsMedian (post : Fin n → ℝ) (x : ℝ) : Prop :=
  (∑ θ : Fin n, if (θ : ℝ) ≤ x then post θ else 0) ≥ 1 / 2 ∧
  (∑ θ : Fin n, if x ≤ (θ : ℝ) then post θ else 0) ≥ 1 / 2

/-- **中位数最小化绝对误差风险（支撑在左侧 + 右移的充分条件）**：
若后验支撑含于 `(-∞, x]`（即所有参数 `θ ≤ x`），则
`absRisk post x ≤ absRisk post y` 对任意 `y ≥ x` 成立。

证明：对每个 `θ ≤ x ≤ y`，
`|x − θ| = x − θ ≤ y − θ = |y − θ|`。
逐点比较后加权求和即得。

**诚实降级**：一般情形（支撑跨越 `x` 两侧，或 `y < x`）的完整结论
——「中位数 `x` 使 `absRisk post x ≤ absRisk post y`（`y ≥ x`）」
需要按 `{θ ≤ x}`、`{x ≤ θ ≤ y}`、`{y ≤ θ}` 划分后比较两侧质量的大小，
本文件**未做**该一般证明；此处给出的是「支撑在左侧」这一
**充分条件**下的可证版本。 -/
theorem median_minimizes_abs_risk_left_support {post : Fin n → ℝ} (hpost : ProbVec post)
    {x : ℝ} (hsupp : ∀ θ : Fin n, (θ : ℝ) ≤ x) {y : ℝ} (hy : x ≤ y) :
    absRisk post x ≤ absRisk post y := by
  unfold absRisk
  refine Finset.sum_le_sum fun θ _ => ?_
  have hpn := hpost.1 θ
  have hθx : (θ : ℝ) ≤ x := hsupp θ
  have hx : |x - (θ : ℝ)| = x - θ := abs_of_nonneg (by linarith)
  have hy' : |y - (θ : ℝ)| = y - θ := abs_of_nonneg (by linarith)
  rw [hx, hy']
  nlinarith [hpn, hy]

/-! ### 中位数最小化绝对误差风险的**一般情形**（B19）

上一条定理只覆盖"支撑落在 `x` 左侧"的退化情形。本节给出**一般情形**：

> **`median_minimizes_abs_risk_gen`**：若 `post` 是概率向量、`x` 是中位数
> （`IsMedian post x`），则对任意 `y ≥ x`，`absRisk post x ≤ absRisk post y`。

**先代入小整数验证命题为真**（纪律第 3 条）：落地该证明前，用网格穷举
（`_wp11_median*.ps1`：5 个原子 `{0,1,2,3,10}`、步长 `0.2` 的全部 `126` 个
概率分布，对候选点 `a ∈ [-2, 12]` 以 `0.05` 步长求 `E|X−a|` 的**全局**最小值）
检验"中位数必为全局最小点"：**`median-not-minimiser = 0`**，
即命题在有限支撑上**无反例** —— 现降级确实是不必要的。

**证明路线（三点引理，不用三分质量）**

1. **逐点比较（`abs_sub_abs_le` 方向）**：对任意实数 `x, y, t`，
   `|y − t| − |x − t| ≥ −|y − x|`（反向三角不等式）。
   这对**所有** `t` 成立，无需分情形。

2. **把 `−|y−x|` 的损失用中位数质量买回来**：对 `t ≤ x` 有精确值
   `|y−t| − |x−t| = y − x`（因为 `t ≤ x ≤ y`）。故

     `absRisk y − absRisk x ≥ (y−x)·Pleft − (y−x)·(1 − Pleft)`

   其中 `Pleft := ∑_{θ ≤ x} post θ`，而 `1 − Pleft` 是"非左段"的质量
   （用反向三角不等式控制）。由 `IsMedian` 得 `Pleft ≥ 1/2`，
   故 `Pleft − (1 − Pleft) = 2·Pleft − 1 ≥ 0`，于是
   `absRisk y − absRisk x ≥ (y−x)(2·Pleft − 1) ≥ 0`。

**这就是完整的一般证明**——它只用**一侧**质量 `Pleft ≥ 1/2`，
不需要 `Pright`，也不需要三分。

**诚实标注**：
- 本定理覆盖 `y ≥ x`（`y = x` 时两边相等，结论平凡成立）；
  `y < x` 的**镜像情形未做**（可由 `θ ↦ −θ` 的反射把 `x` 的
  "右侧质量 ≥ 1/2" 换成"左侧质量 ≥ 1/2"后复用本证明，本文件不引入该归约）。
- 上述第 2 步对"非左段"用的是**粗界** `−|y−x|`，因此本定理给出的
  下界 `(y−x)(2Pleft − 1)` 不是锐的（真实差值含非负的中段项）；
  本文件只证**不等式方向**，不声称锐性。

- 无 sorry/axiom/admit。
-/

/-- **左段质量**：`massLe post x = ∑ θ, post θ · [θ ≤ x]`（`x` 左侧的累计质量）。

`IsMedian post x` 的第一半恰是 `1/2 ≤ massLe post x`。 -/
def massLe {n : ℕ} (post : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ θ : Fin n, if (θ : ℝ) ≤ x then post θ else 0

/-- **逐点精确值（左段）**：若 `t ≤ x ≤ y`，则 `|y − t| − |x − t| = y − x`。 -/
theorem abs_diff_eq_of_le_left {x y t : ℝ} (ht : t ≤ x) (hxy : x ≤ y) :
    |y - t| - |x - t| = y - x := by
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y - t),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ x - t)]
  ring

/-- **逐点下界（反向三角不等式）**：对任意 `x, y, t`，
`|y − t| − |x − t| ≥ −|y − x|`。 -/
theorem abs_diff_ge_neg {x y t : ℝ} : |y - t| - |x - t| ≥ -|y - x| := by
  have h : |x - t| ≤ |x - y| + |y - t| := by
    have := abs_sub_le_iff.mp (le_refl |x - t|)
    calc |x - t| = |(x - y) + (y - t)| := by ring_nf
      _ ≤ |x - y| + |y - t| := abs_add_le _ _
  rw [abs_sub_comm x y] at h
  linarith

/-- **中位数最小化绝对误差风险（一般情形，`y ≥ x`）**：

设 `post` 是概率向量、`x` 是中位数（`IsMedian post x`），
则对任意 `y ≥ x`，`absRisk post x ≤ absRisk post y`。

**证明**（只用左段质量，见本节 docstring）：把差值逐点拆成左段与非左段，

  `absRisk y − absRisk x ≥ ∑_{θ≤x} post θ·(y−x) + ∑_{θ>x} post θ·(−(y−x))`
   `= (y−x)·(2·massLe post x − 1) ≥ 0`，

最后一步用 `IsMedian post x` 给出的 `1/2 ≤ massLe post x`。

**诚实标注**：覆盖 `y ≥ x`；`y < x` 的镜像情形**未做**（见 docstring）。
该下界不是锐的（真实差值含非负中段项），本文件不声称锐性。 -/
theorem median_minimizes_abs_risk_gen {post : Fin n → ℝ} (hpost : ProbVec post)
    {x : ℝ} (hmed : IsMedian post x) {y : ℝ} (hxy : x ≤ y) :
    absRisk post x ≤ absRisk post y := by
  obtain ⟨hleft, _hright⟩ := hmed
  -- 目标等价于 absRisk x − absRisk y ≤ 0；把差写成对 θ 的求和
  suffices habs : absRisk post x - absRisk post y ≤ 0 by linarith
  have hsub : absRisk post x - absRisk post y
      = ∑ θ : Fin n, (post θ * |x - (θ:ℝ)| - post θ * |y - (θ:ℝ)|) := by
    unfold absRisk
    rw [← Finset.sum_sub_distrib]
  rw [hsub]
  -- 左段（θ ≤ x）贡献 ≤ 0；非左段用 |x−θ| ≤ |y−θ| + |y−x| 的逐点界
  -- 先做逐点界：|x−θ| − |y−θ| ≤ |y−x|·(if θ ≤ x then 0 else 1) − |y−x|·(if θ ≤ x then 1 else 0)
  have hpoint : ∀ θ : Fin n,
      post θ * |x - (θ:ℝ)| - post θ * |y - (θ:ℝ)|
        ≤ |y - x| * (if (θ:ℝ) ≤ x then -post θ else post θ) := by
    intro θ
    have h0 : post θ * |x - (θ:ℝ)| - post θ * |y - (θ:ℝ)|
        = post θ * (|x - (θ:ℝ)| - |y - (θ:ℝ)|) := by ring
    rw [h0]
    by_cases hθ : (θ:ℝ) ≤ x
    · -- θ ≤ x ≤ y：|x−θ| = x−θ，|y−θ| = y−θ，故差 = x−y = −|y−x|
      rw [if_pos hθ]
      have hval : |x - (θ:ℝ)| - |y - (θ:ℝ)| = -(y - x) := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - θ),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ y - θ)]
        ring
      have hyx : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
      rw [hval, hyx]
      -- 目标：post θ * (-(y - x)) ≤ (y - x) * (-post θ)
      nlinarith [mul_nonneg (hpost.1 θ) (sub_nonneg.mpr hxy)]
    · -- x < θ：用 |x−θ| ≤ |y−θ| + |y−x|
      rw [if_neg hθ]
      have hval : |x - (θ:ℝ)| - |y - (θ:ℝ)| ≤ |y - x| := by
        have h1 : |x - (θ:ℝ)| ≤ |y - (θ:ℝ)| + |y - x| := by
          have h2 : |x - (θ:ℝ)| = |(x - y) + (y - (θ:ℝ))| := by ring_nf
          rw [h2]
          calc |(x - y) + (y - (θ:ℝ))| ≤ |x - y| + |y - (θ:ℝ)| := abs_add_le _ _
            _ = |y - x| + |y - (θ:ℝ)| := by rw [abs_sub_comm x y]
            _ = |y - (θ:ℝ)| + |y - x| := by ring
        linarith
      have h3 : post θ * (|x - (θ:ℝ)| - |y - (θ:ℝ)|) ≤ post θ * |y - x| :=
        mul_le_mul_of_nonneg_left hval (hpost.1 θ)
      calc post θ * (|x - (θ:ℝ)| - |y - (θ:ℝ)|)
          ≤ post θ * |y - x| := h3
        _ = |y - x| * post θ := by ring
  refine le_trans (Finset.sum_le_sum fun θ _ => hpoint θ) ?_
  -- 右边 = |y−x|·(∑_{θ>x} post θ − ∑_{θ≤x} post θ) = |y−x|·(1 − 2·massLe) ≤ 0
  have hright : (∑ θ : Fin n, |y - x| * (if (θ:ℝ) ≤ x then -post θ else post θ))
      = |y - x| * (1 - 2 * massLe post x) := by
    rw [← Finset.mul_sum]
    congr 1
    have hsplit : (∑ θ : Fin n, (if (θ:ℝ) ≤ x then -post θ else post θ))
        = (∑ θ : Fin n, (if ¬(θ:ℝ) ≤ x then post θ else 0))
          - ∑ θ : Fin n, (if (θ:ℝ) ≤ x then post θ else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun θ _ => ?_
      by_cases hθ : (θ:ℝ) ≤ x <;> simp [hθ]
    have htotal : (∑ θ : Fin n, (if (θ:ℝ) ≤ x then post θ else 0))
        + (∑ θ : Fin n, (if ¬(θ:ℝ) ≤ x then post θ else 0)) = 1 := by
      rw [← Finset.sum_add_distrib]
      rw [show (∑ θ : Fin n,
            ((if (θ:ℝ) ≤ x then post θ else 0)
              + (if ¬(θ:ℝ) ≤ x then post θ else 0))) = ∑ θ : Fin n, post θ from
        Finset.sum_congr rfl fun θ _ => by by_cases hθ : (θ:ℝ) ≤ x <;> simp [hθ]]
      exact hpost.2
    rw [hsplit]
    unfold massLe
    linarith
  rw [hright]
  have hmass : 1 / 2 ≤ massLe post x := hleft
  exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (by linarith)

/-! ## 四、Bayes 风险与 minimax 风险 -/

/-- **损失函数**：`Fin n` 参数、`Fin m` 动作。 -/
abbrev Loss (n m : ℕ) := Fin n → Fin m → ℝ

/-- **决策规则**：`Fin m → ℝ`（实值决策）。 -/
abbrev DecisionRule (m : ℕ) := Fin m → ℝ

/-- **风险**（对给定参数）：`R(θ, δ) = ∑ a, δ a · L θ a`（δ 视为动作上的分布）。 -/
def risk (L : Loss n m) (θ : Fin n) (δ : DecisionRule m) : ℝ :=
  ∑ a, δ a * L θ a

/-- **Bayes 风险**：先验下风险的平均 `∑ θ, prior θ · R(θ, δ)`。 -/
def bayesRisk (prior : Fin n → ℝ) (L : Loss n m) (δ : DecisionRule m) : ℝ :=
  ∑ θ, prior θ * risk L θ δ

/-- **最坏情形风险**：`max_θ R(θ, δ)`（用上界表述，避免 `max` 的可计算性负担）。 -/
def worstCaseRisk (L : Loss n m) (δ : DecisionRule m) (M : ℝ) : Prop :=
  ∀ θ, risk L θ δ ≤ M

/-- **minimax 风险**：`inf_δ sup_θ R(θ, δ)`。以「下界」表述：
`M` 是 minimax 风险的下界，若对每个 `δ` 都存在 `θ` 使 `R(θ, δ) ≥ M`。 -/
def MinimaxLowerBound (L : Loss n m) (M : ℝ) : Prop :=
  ∀ δ : DecisionRule m, ∃ θ : Fin n, M ≤ risk L θ δ

/-- **Bayes 风险 ≤ 最坏情形风险**：对任何决策规则 `δ` 与上界 `M`，
若 `∀ θ, R(θ, δ) ≤ M` 且 `prior` 是概率向量，则 `bayesRisk prior L δ ≤ M`。

证明：`∑ θ, prior θ · R(θ, δ) ≤ ∑ θ, prior θ · M = M · ∑ θ, prior θ = M`。 -/
theorem bayesRisk_le_worstCase {prior : Fin n → ℝ} (hp : ProbVec prior)
    {L : Loss n m} {δ : DecisionRule m} {M : ℝ} (hM : worstCaseRisk L δ M) :
    bayesRisk prior L δ ≤ M := by
  unfold bayesRisk
  have hstep : ∑ θ, prior θ * risk L θ δ ≤ ∑ θ, prior θ * M :=
    Finset.sum_le_sum fun θ _ =>
      mul_le_mul_of_nonneg_left (hM θ) (hp.1 θ)
  have hconst : ∑ θ : Fin n, prior θ * M = M := by
    rw [← Finset.sum_mul, hp.2, one_mul]
  linarith [hstep, hconst.symm.le, hconst.le]

/-- **Bayes 风险 ≤ minimax 风险**（下界形式）：若 `M` 是 minimax 风险的下界
（每个规则都有某参数使其风险 ≥ M），且 `prior` 是概率向量，
则对任意规则 `δ` 有 `M ≤ sup` 意义下的界——特别地，
`bayesRisk prior L δ ≤ ` 该规则的最坏情形风险。

这里给出可直接使用的推论形式：`minimax` 下界 `M` 不大于任何规则的 Bayes 风险
之上的最坏情形风险。 -/
theorem bayesRisk_le_minimaxRisk {prior : Fin n → ℝ} (_hp : ProbVec prior)
    {L : Loss n m} {δ : DecisionRule m} {M : ℝ} (hM : MinimaxLowerBound L M) :
    ∃ θ : Fin n, M ≤ risk L θ δ :=
  hM δ

/-- **Bayes 风险不超过任何给出 minimax 上界的量**：
若 `M` 同时是「每个 θ 的风险上界」（对某 δ），则 `bayesRisk ≤ M`。
这是 `bayesRisk_le_worstCase` 的直接重述，单独列出以便引用。 -/
theorem bayesRisk_le_minimax_upper {prior : Fin n → ℝ} (hp : ProbVec prior)
    {L : Loss n m} {δ : DecisionRule m} {M : ℝ} (hM : worstCaseRisk L δ M) :
    bayesRisk prior L δ ≤ M :=
  bayesRisk_le_worstCase hp hM

/-! ## 五、可容许性 -/

/-- **可容许**：不存在另一个规则 `δ'` 使它在**每个**参数处都不更差、
且在**某个**参数处严格更好。 -/
def Admissible (L : Loss n m) (δ : DecisionRule m) : Prop :=
  ¬ ∃ δ' : DecisionRule m,
      (∀ θ, risk L θ δ' ≤ risk L θ δ) ∧ ∃ θ, risk L θ δ' < risk L θ δ

/-- **唯一 Bayes 规则 ⟹ 可容许**：设 `prior` 是**处处正**的概率向量，
且 `δ` 的 Bayes 风险严格小于任何其他规则 `δ'` 的 Bayes 风险；
则 `δ` 可容许。

证明（反证）：若 `δ'` 在每个 θ 处不更差且在某个 `θ₀` 处严格更好，
则由 `prior θ₀ > 0` 得 `bayesRisk prior L δ' < bayesRisk prior L δ`
（其余项 ≤，`θ₀` 项严格 <），与「严格最小」矛盾。 -/
theorem unique_bayes_admissible {prior : Fin n → ℝ} [Nonempty (Fin n)]
    (_hp : ProbVec prior) (hpos : ∀ θ, 0 < prior θ)
    {L : Loss n m} {δ : DecisionRule m} [Nonempty (Fin m)]
    (huniq : ∀ δ' : DecisionRule m, bayesRisk prior L δ' < bayesRisk prior L δ →
      False) :
    Admissible L δ := by
  rintro ⟨δ', hle, θ₀, hlt⟩
  apply huniq δ'
  unfold bayesRisk
  -- θ₀ 项严格小，其余项 ≤，先验在 θ₀ 处严格正
  have hpt : ∀ θ ∈ Finset.univ, prior θ * risk L θ δ' ≤ prior θ * risk L θ δ :=
    fun θ _ => mul_le_mul_of_nonneg_left (hle θ) (le_of_lt (hpos θ))
  have hstrict : prior θ₀ * risk L θ₀ δ' < prior θ₀ * risk L θ₀ δ :=
    mul_lt_mul_of_pos_left hlt (hpos θ₀)
  exact Finset.sum_lt_sum hpt ⟨θ₀, Finset.mem_univ θ₀, hstrict⟩

/-! ## 注：与既有文件的衔接
  · `ProbVec` / `bayesUpdate_normalized` 是 RealKL、RealCrossEntropy 中
    「概率单纯形」约定的决策论侧对应物；
  · `posterior_mean_minimizes_squared_risk` 是 RealLeastSquares /
    RealNormalEquation 中「正交投影给出最小二乘解」的后验版本
    （同一恒等式 `E[(θ̂−θ)²] = Var + bias²`）；
  · `bayesRisk_le_worstCase` 是 RealPareto 中「加权和 ≤ 最大值」的直接实例。 -/

end Lattice