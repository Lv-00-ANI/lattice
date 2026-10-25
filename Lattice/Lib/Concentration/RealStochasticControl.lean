import Mathlib
import Lattice.Lib.Optim.RealValueIteration
import Lattice.Lib.LearningTheory.RealBayesOptimality
/-!
# LATTICE: 随机控制（有限时域 / 有限状态 / 确定性转移）—— Bellman 方程与最优性原理

**项目约束**：连续时间 HJB 需要粘性解理论（mathlib 4.14 无），
故本文件只做**有限时域、有限状态、确定性转移**的**离散**随机控制。
在这一层上，全部内容都是**纯组合 + 有限归纳**，因而**无条件可证**。

## 模型（确定性转移）

- 状态集 `Fin n`，动作集 `Fin m`，时域 `t = 0, 1, …, T`（`T` 步）；
- 转移 `step : Fin n → Fin m → Fin n`（**确定性**：给定状态与动作，下一步状态唯一）；
- 单步代价 `cost : Fin n → Fin m → ℝ`；
- 终值 `terminal : Fin n → ℝ`。

连续时间 HJB `−∂_t V = min_u {c(x,u) + ∇V·f(x,u)}` 的**离散对应物**是
    `V_t(x) = min_u { c(x,u) + V_{t+1}(step x u) }`，`V_T = terminal`。

## 内容

  1. `V`（def）：值时函数，由**反向归纳**定义（`V t x` 表示「还剩 `t` 步」时的最优值）；
  2. `bellman_residual`（def）：Bellman 方程两侧之差；
  3. `bellman_equation`（**核心**）：反向归纳定义确实满足 Bellman 方程
     `V (t+1) x = min_u { c(x,u) + V t (step x u) }`；
  4. `bellman_optimal_action_exists`：有限动作集上最小值**可达**
     （存在实现最优的动作 `u*`）——用 `Finset.exists_min_image`；
  5. `optimality_principle`（**最优性原理，核心**）：若策略 `π` 在时刻 `t+1`
     之后是最优的（其剩余代价等于 `V`），则向前延拓一步得到的策略仍最优，
     且其时刻 `t` 的值恰为 `c(x,π x) + V (t+1) (step x (π x))`。
     这是 Bellman 最优性原理的**可证离散形式**；
  6. `bellman_monotone`：Bellman 后向算子在**逐点序**下单调
     （`f ≤ g ⟹ B f ≤ B g`）——值迭代收敛的序结构基础；
  7. `deterministic_reduction`：与既有 `RealValueIteration` 的**接口**——
     当动作集退化为单元素（无选择）时，本文件的 `V` 退化为
     `RealValueIteration.BellmanOp` 的确定性特例（`P` 为确定性转移矩阵）。

## 与 `RealValueIteration` 的接口，及与 `RealDecisionTheory` 的关系

- `RealValueIteration` 处理**无限时域折扣** Bellman 算子 `T(V)(s) = R(s) + γΣP V`
  及其**收缩性**（∞ 范数）；
- 本文件处理**有限时域反向归纳**（无折扣）`V_{t+1} = min_u{c + V_t∘step}`。
  二者是 Bellman 理论的两个不同侧面：前者给**收敛**（折扣 ⟹ 收缩），
  后者给**最优性原理**（有限 ⟹ 归纳）。
- `RealBayesOptimality` 的 `ProbVec` 提供了「概率向量」的现成定义
  （本文件第 3 行 import）。「随机化动作不优于确定最优动作」的结论
  `randomization_not_better` 在本文件**自证**：`RealDecisionTheory`
  的 `weighted_avg_le_max` 与之同构，但该模块有编译缺陷且**未被 import**，
  故此处不依赖它。

## 诚实边界（本文件不证 / 不声称的）

- **不做**：连续时间 HJB `−∂_t V = min_u{c + ∇V·f}`（需粘性解理论，
  mathlib 4.14 无；连 `HamiltonJacobi` 相关 API 都不存在）。
- **不做**：**随机**转移（`P(s'|s,u)`）下的一般 Bellman 方程。
  本文件的转移是**确定性函数** `step`，故 Bellman 方程无需期望算子。
  随机转移需要「有限期望 + 逐点取 min」，其额外内容是
  `E[V(s')] = Σ_{s'} P(s'|s,u)·V(s')` 的线性性——本文件**未做**该归约
  （既未把随机转移写成确定性动作索引的凸平均，也未展开完整随机 MDP 理论）。
  第五节只给出 `randomization_not_better` 与 `bellman_value_is_lower_bound`，
  二者论证的是 Bellman 方程中「取 `min` 而非取期望」的正当性，
  而非随机转移的 Bellman 方程本身。
- **不做**：无限时域、无折扣的 Bellman（需**停时/可达性**条件，
  否则 `V ≡ −∞`；这是真实的数学障碍，不是技术限制）。
- 动作集 / 状态集**有限**（`Fin n`、`Fin m`）；「min 可达」依赖有限性，
  是**有限维特有的**结论（无限动作集需紧性 + 下半连续性）。
- 无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n m : ℕ}

-- 动作集 `Fin m` 必须非空（否则 `min_u` 无意义、`inf'` 无定义）。
-- 这是**语义必需**的假设，不是技术妥协：空动作集的最优控制问题无定义。
variable [Nonempty (Fin m)]

/-! ## 第一节：值时函数（反向归纳定义）与 Bellman 方程

`V t x` = 「从状态 `x` 出发、还剩 `t` 步决策」时的**最优累积代价**。
递归：`V 0 = terminal`（无剩余步 ⟹ 只剩终值），
`V (t+1) x = min_u { cost x u + V t (step x u) }`。

注意方向：这里 `V` 按「**剩余**步数」递归，与常见的「时刻」递归等价但更便于归纳
（`V (t+1)` 直接引用 `V t`，是**结构递归**，不需要良基论证）。 -/

/-- **确定性转移**：`step x u` 是在状态 `x` 采取动作 `u` 后的下一状态。 -/
def ctlStep (step : Fin n → Fin m → Fin n) (x : Fin n) (u : Fin m) : Fin n := step x u

/-- **Bellman 反向算子**：`B W x = min_u { cost x u + W (step x u) }`。
这是连续时间 HJB 右端 `min_u{c(x,u) + ∇V·f(x,u)}` 的离散对应物。 -/
def bellmanBackward (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (W : Fin n → ℝ) (x : Fin n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun u => cost x u + W (step x u))

/-- **值时函数**：按**剩余步数**反向归纳。
`V 0 = terminal`，`V (t+1) = bellmanBackward (V t)`。 -/
def ctlValue (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => terminal
  | (t + 1) => bellmanBackward step cost (ctlValue step cost terminal t)

/-! ## 第二节：Bellman 方程与最小值可达性 -/

/-- 🎯 **Bellman 方程（核心）**：
`V (t+1) x = min_u { cost x u + V t (step x u) }` —— 由 `ctlValue` 的定义即得。

这正是有限时域 HJB 的离散形式（无折扣、确定性转移）。
注意它是**恒等式（rfl 级）**：反向归纳定义本身就**是** Bellman 方程，
这体现了「有限时域的最优性原理不含分析内容」这一事实。 -/
theorem bellman_equation (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (t : ℕ) (x : Fin n) :
    ctlValue step cost terminal (t + 1) x
      = Finset.univ.inf' Finset.univ_nonempty (fun u => cost x u + ctlValue step cost terminal t (step x u)) :=
  rfl

/-- **最小值可达（存在最优动作）**：有限动作集上，必然存在动作 `u*` 达到下确界
（`Finset.exists_mem_eq_inf'`）。这对应 HJB 里「`min` 可达」的紧性条件——
在**有限**动作集上它是**自动**的。 -/
theorem bellman_optimal_action_exists (step : Fin n → Fin m → Fin n)
    (cost : Fin n → Fin m → ℝ) (terminal : Fin n → ℝ) (t : ℕ) (x : Fin n) :
    ∃ u : Fin m,
      ctlValue step cost terminal (t + 1) x
        = cost x u + ctlValue step cost terminal t (step x u) := by
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun u => cost x u + ctlValue step cost terminal t (step x u))
  exact ⟨u, by rw [ctlValue, show bellmanBackward step cost (ctlValue step cost terminal t) x
    = Finset.univ.inf' Finset.univ_nonempty
        (fun u => cost x u + ctlValue step cost terminal t (step x u)) from rfl, hu]⟩

/-- **逐点下界刻画**：`V (t+1) x ≤ cost x u + V t (step x u)` 对所有 `u` 成立
—— 即 `V` 是 Bellman 方程的**下解**（任何动作都给出一个上界）。 -/
theorem bellman_le_action (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (t : ℕ) (x : Fin n) (u : Fin m) :
    ctlValue step cost terminal (t + 1) x
      ≤ cost x u + ctlValue step cost terminal t (step x u) :=
  Finset.inf'_le (fun u => cost x u + ctlValue step cost terminal t (step x u))
    (Finset.mem_univ u)

/-! ## 第三节：Bellman 后向算子的单调性

`f ≤ g`（逐点）⟹ `B f ≤ B g`（逐点）。这是**值迭代收敛**的序结构基础：
后向算子保序，配合收敛性定理（如 `RealValueIteration` 的收缩）即得迭代收敛。 -/

/-- 🎯 **Bellman 后向算子的单调性**：`W₁ ≤ W₂`（逐点）⟹ `B W₁ ≤ B W₂`（逐点）。

证明：取 `W₂` 侧达到最小的动作 `u*`（`exists_mem_eq_inf'`）。
则 `B W₂ x = cost x u* + W₂ (step x u*)`，而 `B W₁ x ≤ cost x u* + W₁ (step x u*)`
（`inf'_le`），后者由 `h` 被前者界住。 -/
theorem bellman_monotone (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    {W₁ W₂ : Fin n → ℝ} (h : ∀ y, W₁ y ≤ W₂ y) (x : Fin n) :
    bellmanBackward step cost W₁ x ≤ bellmanBackward step cost W₂ x := by
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun u => cost x u + W₂ (step x u))
  unfold bellmanBackward
  rw [hu]
  exact le_trans (Finset.inf'_le (fun u => cost x u + W₁ (step x u)) (Finset.mem_univ u))
    (add_le_add_left (h (step x u)) _)

/-- **单调性的迭代形式**：`W₁ ≤ W₂` ⟹ 迭代 `t` 次后仍逐点保序。 -/
theorem bellman_monotone_iterate (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    {W₁ W₂ : Fin n → ℝ} (h : ∀ y, W₁ y ≤ W₂ y) :
    ∀ t y, (bellmanBackward step cost)^[t] W₁ y ≤ (bellmanBackward step cost)^[t] W₂ y := by
  intro t
  induction t with
  | zero => simpa using h
  | succ t ih =>
      intro y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact bellman_monotone step cost ih y

/-! ## 第四节：最优性原理（有限时域）

**Bellman 最优性原理**：若一个策略在「剩下的 `t` 步」上是最优的，
那么在「剩下的 `t+1` 步」上，最优策略可以写成
「先选一个使 `c(x,u) + V t (step x u)` 最小的动作，其后再按 `t` 步最优策略走」。

本节的 `optimality_principle` 把「策略」实现为**动作选取函数**
`π : Fin n → Fin m`，其剩余代价按**确定性展开**递归定义。 -/

/-- **策略的剩余代价**：按策略 `π` 走 `t` 步的累积代价（含终值）。 -/
def policyCost (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (π : Fin n → Fin m) : ℕ → Fin n → ℝ
  | 0 => terminal
  | (t + 1) => fun x => cost x (π x) + policyCost step cost terminal π t (step x (π x))

/-- **策略最优性**：策略 `π` 在剩余 `t` 步上达到最优值 `V t`。 -/
def IsOptimalPolicy (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (π : Fin n → Fin m) (t : ℕ) : Prop :=
  ∀ x, policyCost step cost terminal π t x = ctlValue step cost terminal t x

/-- **`V` 定义域里的 Bellman 最优动作**：对每个 `(t+1, x)`，
选一个达到 `inf'` 的动作作为策略值。 -/
def bellmanGreedy (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (t : ℕ) (x : Fin n) : Fin m :=
  Classical.choose (bellman_optimal_action_exists step cost terminal t x)

/-- **贪心动作确实达到下确界**。 -/
theorem bellmanGreedy_spec (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (t : ℕ) (x : Fin n) :
    ctlValue step cost terminal (t + 1) x
      = cost x (bellmanGreedy step cost terminal t x)
        + ctlValue step cost terminal t (step x (bellmanGreedy step cost terminal t x)) :=
  Classical.choose_spec (bellman_optimal_action_exists step cost terminal t x)

/-- 🎯 **最优性原理（核心，前向延拓）**：
设策略 `π` 在剩余 `t` 步上最优（`IsOptimalPolicy … π t`）。
则对**任意**状态 `x`，只要动作 `u` 在 `x` 处达到 `V (t+1) x` 的下确界，
就有
    `V (t+1) x = c(x,u) + policyCost π t (step x u)`。

即：**最优策略 = 一步贪心 + 其后最优**——这正是 Bellman 最优性原理。
证明是纯粹的代数替换（贪心方程 + `π` 的最优性）。 -/
theorem optimality_principle (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (π : Fin n → Fin m) (t : ℕ)
    (hπ : IsOptimalPolicy step cost terminal π t) (x : Fin n) (u : Fin m)
    (hu : ctlValue step cost terminal (t + 1) x
      = cost x u + ctlValue step cost terminal t (step x u)) :
    ctlValue step cost terminal (t + 1) x
      = cost x u + policyCost step cost terminal π t (step x u) := by
  rw [hu, hπ (step x u)]

/-- 🎯 **最优性原理（贪心策略版）**：
由 `optimality_principle`，只要存在一个在 `t` 步上最优的策略 `π`，
则**贪心策略**（先取 `bellmanGreedy`，再跟随 `π`）在 `t+1` 步上最优。

这给出「最优策略可以**逐步构造**」的结论——从终值出发，
每往前推一步就贪心选一次动作，得到的策略在每个时点都是最优的。 -/
theorem optimality_principle_greedy (step : Fin n → Fin m → Fin n)
    (cost : Fin n → Fin m → ℝ) (terminal : Fin n → ℝ) (π : Fin n → Fin m) (t : ℕ)
    (hπ : IsOptimalPolicy step cost terminal π t) :
    ∀ x, cost x (bellmanGreedy step cost terminal t x)
        + policyCost step cost terminal π t (step x (bellmanGreedy step cost terminal t x))
      = ctlValue step cost terminal (t + 1) x := by
  intro x
  rw [bellmanGreedy_spec step cost terminal t x, hπ (step x (bellmanGreedy step cost terminal t x))]

/-- **终值处的最优性（归纳基）**：任意策略在 `0` 步上「最优」
（此时代价就是终值，与策略无关）。 -/
theorem isOptimalPolicy_zero (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (π : Fin n → Fin m) :
    IsOptimalPolicy step cost terminal π 0 :=
  fun _ => rfl

/-! ## 第五节：随机化动作不优于确定性最优

在有限动作集上，「按概率分布随机选动作」的期望代价**不低于**最优确定性动作。
这与 `RealDecisionTheory.weighted_avg_ge_min` **同构**，但本文件**自证**
（该模块未被 import，亦未被调用），
也是 HJB 里「`min` 而非平均」的正当性来源：
**随机化不能改善最优值**（对期望代价准则）。 -/

/-- 🎯 **随机化不优于最优（最小化版）**：若 `w` 是概率向量（`ProbVec w`），
则任何随机化策略的期望代价**不低于**最优确定性动作的代价：
    `cost x u₀ + V t (step x u₀) ≤ Σ_u w_u·(cost x u + V t (step x u))`
（`u₀` 为任一使 `c(x,u) + V t (step x u)` 取最小的动作）。

这证明 Bellman 方程里用 `min`（而非对动作取期望）是**正当**的。

**接口说明**：`RealDecisionTheory.weighted_avg_ge_min` 是本结论在一般
`Fin k` 上的现成形式，但该模块当前**有编译缺陷**（见最终报告），
故此处**自证**同样的加权平均–最小值界（证明与原版同构），
避免对不可用模块的依赖。 -/
theorem randomization_not_better (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (terminal : Fin n → ℝ) (t : ℕ) (x : Fin n) (w : Fin m → ℝ)
    (hw : ProbVec w) (u₀ : Fin m)
    (hu₀ : ∀ u, cost x u₀ + ctlValue step cost terminal t (step x u₀)
      ≤ cost x u + ctlValue step cost terminal t (step x u)) :
    cost x u₀ + ctlValue step cost terminal t (step x u₀)
      ≤ ∑ u, w u * (cost x u + ctlValue step cost terminal t (step x u)) := by
  have hmin : Finset.univ.inf' Finset.univ_nonempty
      (fun u => cost x u + ctlValue step cost terminal t (step x u))
      ≤ ∑ u, w u * (cost x u + ctlValue step cost terminal t (step x u)) := by
    have hle : ∀ u ∈ (Finset.univ : Finset (Fin m)),
        (∑ v, w v) * (Finset.univ.inf' Finset.univ_nonempty
            (fun u => cost x u + ctlValue step cost terminal t (step x u)))
          ≤ ∑ v, w v * (cost x v + ctlValue step cost terminal t (step x v)) := by
      intro u _
      calc (∑ v, w v) * (Finset.univ.inf' Finset.univ_nonempty
              (fun u => cost x u + ctlValue step cost terminal t (step x u)))
          = ∑ v, w v * (Finset.univ.inf' Finset.univ_nonempty
              (fun u => cost x u + ctlValue step cost terminal t (step x u))) := by
            rw [Finset.sum_mul]
        _ ≤ ∑ v, w v * (cost x v + ctlValue step cost terminal t (step x v)) :=
            Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left
              (Finset.inf'_le (fun u => cost x u + ctlValue step cost terminal t (step x u))
                (Finset.mem_univ v)) (hw.1 v))
    calc Finset.univ.inf' Finset.univ_nonempty
          (fun u => cost x u + ctlValue step cost terminal t (step x u))
        = (∑ v, w v) * (Finset.univ.inf' Finset.univ_nonempty
            (fun u => cost x u + ctlValue step cost terminal t (step x u))) := by
          rw [hw.2, one_mul]
      _ ≤ ∑ v, w v * (cost x v + ctlValue step cost terminal t (step x v)) :=
          hle (Classical.arbitrary (Fin m)) (Finset.mem_univ _)
  -- 取达到下确界的动作 `ustar`（有限性保证存在），避免直接写 `inf'` 项
  obtain ⟨ustar, _, hustar⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun v => cost x v + ctlValue step cost terminal t (step x v))
  have harg : cost x u₀ + ctlValue step cost terminal t (step x u₀)
      ≤ cost x ustar + ctlValue step cost terminal t (step x ustar) := hu₀ ustar
  have hmin' : cost x ustar + ctlValue step cost terminal t (step x ustar)
      ≤ ∑ u, w u * (cost x u + ctlValue step cost terminal t (step x u)) := by
    rw [← hustar]; exact hmin
  exact le_trans harg hmin'

/-- **Bellman 值是随机化下的下界**：
`V (t+1) x` 同时是（a）所有确定性动作代价的下确界，
且（b）所有随机化期望代价的下界（由 `bellman_le_action` 加权即得）。 -/
theorem bellman_value_is_lower_bound (step : Fin n → Fin m → Fin n)
    (cost : Fin n → Fin m → ℝ) (terminal : Fin n → ℝ) (t : ℕ) (x : Fin n)
    (w : Fin m → ℝ) (hw : ProbVec w) :
    ctlValue step cost terminal (t + 1) x
      ≤ ∑ u, w u * (cost x u + ctlValue step cost terminal t (step x u)) := by
  calc ctlValue step cost terminal (t + 1) x
      = (∑ u, w u) * ctlValue step cost terminal (t + 1) x := by
        rw [show (∑ u, w u) = 1 from hw.2, one_mul]
    _ = ∑ u, w u * ctlValue step cost terminal (t + 1) x := Finset.sum_mul ..
    _ ≤ ∑ u, w u * (cost x u + ctlValue step cost terminal t (step x u)) :=
        Finset.sum_le_sum (fun u _ =>
          mul_le_mul_of_nonneg_left (bellman_le_action step cost terminal t x u) (hw.1 u))

/-! ## 第六节：与 `RealValueIteration` 的接口

`RealValueIteration` 的 Bellman 算子处理**随机转移 + 折扣**：
`BellmanOp P R γ V s = R s + γ·Σ_{s'} P s s'·V s'`。
本文件的 `bellmanBackward` 处理**确定性转移 + 无折扣 + min**。

两者在「动作集退化为单点、转移退化为确定性」时一致：
取 `R := fun s => cost s u₀`、`γ := 1`、`P s s' := if step s u₀ = s' then 1 else 0`，
则 `BellmanOp P R 1 V s = cost s u₀ + V (step s u₀)`。
下面的 `deterministic_reduction` 确立该等式，从而
`RealValueIteration` 的**收缩性**结论（在 `γ < 1` 时）可用于本文件的
折扣推广；而无折扣（`γ = 1`）情形本文件用**有限归纳**处理，无需收缩。 -/

/-- **确定性转移矩阵**：`detP step u₀ s s' = if step s u₀ = s' then 1 else 0`。 -/
def detP (step : Fin n → Fin m → Fin n) (u₀ : Fin m) (s s' : Fin n) : ℝ :=
  if step s u₀ = s' then 1 else 0

omit [Nonempty (Fin m)] in
/-- **确定性转移矩阵是行随机的**（`RealValueIteration` 的前提之一）。 -/
theorem detP_row_sum (step : Fin n → Fin m → Fin n) (u₀ : Fin m) (s : Fin n) :
    ∑ s' : Fin n, detP step u₀ s s' = 1 := by
  have h : ∀ s' : Fin n,
      detP step u₀ s s' = if s' = step s u₀ then (1 : ℝ) else 0 := by
    intro s'
    unfold detP
    by_cases hc : step s u₀ = s'
    · rw [if_pos hc, if_pos hc.symm]
    · rw [if_neg hc, if_neg (fun hh => hc hh.symm)]
  rw [Finset.sum_congr rfl (fun s' _ => h s')]
  rw [Finset.sum_ite_eq' Finset.univ (step s u₀) (fun _ => (1 : ℝ))]
  simp

omit [Nonempty (Fin m)] in
/-- **确定性转移矩阵非负**（`RealValueIteration` 的另一前提）。 -/
theorem detP_nonneg (step : Fin n → Fin m → Fin n) (u₀ : Fin m) (s s' : Fin n) :
    0 ≤ detP step u₀ s s' := by
  unfold detP
  split <;> norm_num

omit [Nonempty (Fin m)] in
/-- 🎯 **与 `RealValueIteration.BellmanOp` 的归约（接口定理）**：
固定动作 `u₀`、令 `R s = cost s u₀`、`γ = 1`、`P = detP step u₀`，则
    `BellmanOp P R 1 V s = cost s u₀ + V (step s u₀)`。

即：**确定性单动作控制 = `RealValueIteration` 的 Bellman 算子在 `γ = 1` 的特例**。
因此 `RealValueIteration` 的收缩/收敛结论与有限时域归纳结论
在同一模型上彼此一致（前者需 `γ < 1`，后者不需）。 -/
theorem deterministic_reduction (step : Fin n → Fin m → Fin n) (cost : Fin n → Fin m → ℝ)
    (u₀ : Fin m) (V : Fin n → ℝ) (s : Fin n) :
    BellmanOp (detP step u₀) (fun s => cost s u₀) 1 V s = cost s u₀ + V (step s u₀) := by
  have h : ∀ s' : Fin n,
      detP step u₀ s s' * V s' = (if s' = step s u₀ then V s' else 0) := by
    intro s'
    unfold detP
    by_cases hc : step s u₀ = s'
    · rw [if_pos hc, if_pos hc.symm, one_mul]
    · rw [if_neg hc, if_neg (fun hh => hc hh.symm), zero_mul]
  unfold BellmanOp
  rw [Finset.sum_congr rfl (fun s' _ => h s')]
  rw [Finset.sum_ite_eq' Finset.univ (step s u₀) (fun s' => V s')]
  simp

end Lattice
