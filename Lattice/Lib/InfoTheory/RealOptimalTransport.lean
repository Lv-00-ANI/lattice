import Mathlib
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 有限支撑最优传输（Kantorovich 问题）

本文件在**有限**概率空间上形式化最优传输（Optimal Transport, OT）的
Kantorovich 松弛问题，并给出以下**已真证**的主结果：

1. `IsTransportPlan`：传输计划（耦合）的定义 —— 非负、边缘分别等于 `p`、`q`；
2. `transportCost`：给定代价 `c` 下计划 `π` 的总代价；
3. `productPlan_isPlan` / `transportPlan_nonempty`：乘积计划可行 ⟹ 可行集**非空**；
4. `transportPlan_convex`：可行集是**凸集**；
5. `exists_optimal_plan`：当 `p, q` 是概率向量（非负且和为 1）时，
   最优传输计划**存在**（可行集在有限维空间 `α → β → ℝ` 中闭且有界 ⟹ 紧，
   代价泛函连续 ⟹ 取到最小值）；
6. `dual_weak`：**对偶弱定理**（Kantorovich 松弛的下界方向），
   对任意可行 `π` 与任意满足 `f a + g b ≤ c a b` 的 `(f, g)`，
   `∑ a, f a * p a + ∑ b, g b * q b ≤ transportCost c π`；
7. `dual_weak_optimal`：把 `dual_weak` 用在最优计划上，得 `max_{f,g} ≤ min_π`。

诚实边界（标注）：
- 本文件**未做**强对偶（`max = min`）与最优 Kantorovich 势的具体构造；
  `exists_optimal_plan` 只断言最优计划存在，不给显式算法；
  相应内容标注为「未做」。
- `exists_optimal_plan` 的假设是 `p, q` 为概率向量（非负、和为 1）。
  一般有限测度（`∑ p = ∑ q` 但不必为 1）的版本未证，标注为「未证」。
- 全部声明无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## 零、坐标投影的连续性 -/

/-- 坐标投影 `π ↦ π a b` 在 `α → β → ℝ` 上是连续的。 -/
theorem continuous_apply₂ (a : α) (b : β) :
    Continuous fun π : α → β → ℝ => π a b := by
  have h1 : Continuous fun π : α → β → ℝ => π a := continuous_apply a
  have h2 : Continuous fun f : β → ℝ => f b := continuous_apply b
  exact h2.comp h1

/-! ## 一、定义：传输计划与传输代价 -/

/-- 传输计划（Kantorovich 耦合）：`π : α → β → ℝ` 是 `p`（边缘在 `α` 上）与
`q`（边缘在 `β` 上）的耦合，当且仅当
1. 每个分量非负：`∀ a b, 0 ≤ π a b`；
2. 行边缘：`∀ a, ∑ b, π a b = p a`；
3. 列边缘：`∀ b, ∑ a, π a b = q b`。 -/
def IsTransportPlan (p : α → ℝ) (q : β → ℝ) (π : α → β → ℝ) : Prop :=
  (∀ a b, 0 ≤ π a b) ∧ (∀ a, ∑ b, π a b = p a) ∧ (∀ b, ∑ a, π a b = q b)

/-- 计划 `π` 在代价函数 `c : α → β → ℝ` 下的总传输代价 `∑ a, ∑ b, π a b * c a b`。 -/
def transportCost (c : α → β → ℝ) (π : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, π a b * c a b

/-- 可行集的**闭性**：`IsTransportPlan p q` 是有限个闭条件（非负性 + 两组线性等式）
的交，因此 `{π | IsTransportPlan p q π}` 在 `α → β → ℝ` 中是闭集。 -/
theorem isClosed_setOf_isTransportPlan (p : α → ℝ) (q : β → ℝ) :
    IsClosed {π : α → β → ℝ | IsTransportPlan p q π} := by
  have h1 : IsClosed {π : α → β → ℝ | ∀ a b, 0 ≤ π a b} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun a => ?_
    rw [Set.setOf_forall]
    exact isClosed_iInter fun b =>
      isClosed_Ici.preimage (continuous_apply₂ a b)
  have h2 : IsClosed {π : α → β → ℝ | ∀ a, ∑ b, π a b = p a} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun a => ?_
    exact isClosed_eq
      (continuous_finset_sum _ fun b _ => continuous_apply₂ a b)
      continuous_const
  have h3 : IsClosed {π : α → β → ℝ | ∀ b, ∑ a, π a b = q b} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun b => ?_
    exact isClosed_eq
      (continuous_finset_sum _ fun a _ => continuous_apply₂ a b)
      continuous_const
  have heq : {π : α → β → ℝ | IsTransportPlan p q π} =
      {π : α → β → ℝ | ∀ a b, 0 ≤ π a b} ∩
        {π : α → β → ℝ | ∀ a, ∑ b, π a b = p a} ∩
          {π : α → β → ℝ | ∀ b, ∑ a, π a b = q b} := by
    ext π
    constructor
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    · intro h
      exact ⟨h.1.1, h.1.2, h.2⟩
  rw [heq]
  exact (h1.inter h2).inter h3

/-- 可行集的**有界性**：由行边缘 `∑ b, π a b = p a` 与非负性，
`π a b ≤ ∑ b, π a b = p a ≤ |p a| ≤ ∑ a, |p a|`，
故可行集包含在以原点为心、`∑ a, |p a|` 为半径的闭球内。 -/
theorem isBounded_setOf_isTransportPlan (p : α → ℝ) (q : β → ℝ) :
    Bornology.IsBounded {π : α → β → ℝ | IsTransportPlan p q π} := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : α → β → ℝ)]
  refine ⟨∑ a, |p a|, ?_⟩
  intro π hπ
  rw [Metric.mem_closedBall]
  have hR : 0 ≤ ∑ a, |p a| := Finset.sum_nonneg fun a _ => abs_nonneg (p a)
  rw [dist_pi_le_iff hR]
  intro a
  rw [dist_pi_le_iff hR]
  intro b
  rw [show (0 : α → β → ℝ) a b = 0 from rfl, dist_zero_right, Real.norm_eq_abs]
  have habs : |π a b| = π a b := abs_of_nonneg (hπ.1 a b)
  rw [habs]
  calc π a b ≤ ∑ b', π a b' :=
        Finset.single_le_sum (fun b' _ => hπ.1 a b') (Finset.mem_univ b)
    _ = p a := hπ.2.1 a
    _ ≤ |p a| := le_abs_self (p a)
    _ ≤ ∑ a', |p a'| := Finset.single_le_sum (fun a' _ => abs_nonneg (p a')) (Finset.mem_univ a)

/-- 可行集的**紧性**：由闭性 + 有界性（有限维空间是 proper 空间，Heine–Borel）。 -/
theorem isCompact_setOf_isTransportPlan (p : α → ℝ) (q : β → ℝ) :
    IsCompact {π : α → β → ℝ | IsTransportPlan p q π} :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_setOf_isTransportPlan p q, isBounded_setOf_isTransportPlan p q⟩

/-! ## 二、可行集非空：乘积计划 -/

/-- **乘积计划可行**：若 `p, q` 是非负且和为 1 的概率向量，
则乘积计划 `π a b = p a * q b` 是一个传输计划。 -/
theorem productPlan_isPlan (p : α → ℝ) (q : β → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    IsTransportPlan p q (fun a b => p a * q b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact mul_nonneg (hp0 a) (hq0 b)
  · intro a
    rw [← Finset.mul_sum, hq1, mul_one]
  · intro b
    rw [← Finset.sum_mul, hp1, one_mul]

/-- **可行集非空**（存在形式）：概率向量 `p, q` 的传输计划集非空。 -/
theorem transportPlan_nonempty (p : α → ℝ) (q : β → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    ∃ π : α → β → ℝ, IsTransportPlan p q π :=
  ⟨fun a b => p a * q b, productPlan_isPlan p q hp0 hp1 hq0 hq1⟩

/-! ## 三、可行集的凸性 -/

/-- **可行集是凸集**：两个传输计划的凸组合仍是传输计划。 -/
theorem transportPlan_convex (p : α → ℝ) (q : β → ℝ)
    (π₁ π₂ : α → β → ℝ) (t : ℝ)
    (h₁ : IsTransportPlan p q π₁) (h₂ : IsTransportPlan p q π₂)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsTransportPlan p q (fun a b => t * π₁ a b + (1 - t) * π₂ a b) := by
  have ht0' : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact add_nonneg (mul_nonneg ht0 (h₁.1 a b)) (mul_nonneg ht0' (h₂.1 a b))
  · intro a
    rw [Finset.sum_add_distrib]
    have e1 : ∑ b, t * π₁ a b = t * p a := by rw [← Finset.mul_sum, h₁.2.1]
    have e2 : ∑ b, (1 - t) * π₂ a b = (1 - t) * p a := by rw [← Finset.mul_sum, h₂.2.1]
    rw [e1, e2]
    ring
  · intro b
    rw [Finset.sum_add_distrib]
    have e1 : ∑ a, t * π₁ a b = t * q b := by rw [← Finset.mul_sum, h₁.2.2]
    have e2 : ∑ a, (1 - t) * π₂ a b = (1 - t) * q b := by rw [← Finset.mul_sum, h₂.2.2]
    rw [e1, e2]
    ring

/-! ## 四、最优传输计划的存在性

可行集 `{π | IsTransportPlan p q π}` 非空、闭、有界（有限维 ⟹ 紧），
`transportCost c` 连续（有限和 + 投影连续），由极值定理取到最小值。 -/

/-- **最优传输计划存在**：概率向量 `p, q` 与任意代价 `c` 下，
存在可行计划 `π*` 使 `transportCost c π*` 在可行集上取最小值。 -/
theorem exists_optimal_plan (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    ∃ π : α → β → ℝ, IsTransportPlan p q π ∧
      ∀ π' : α → β → ℝ, IsTransportPlan p q π' →
        transportCost c π ≤ transportCost c π' := by
  have hcont : Continuous fun π : α → β → ℝ => transportCost c π := by
    simp only [transportCost]
    exact continuous_finset_sum _ fun a _ =>
      continuous_finset_sum _ fun b _ =>
        (continuous_apply₂ a b).mul continuous_const
  obtain ⟨π, hπ, hmin⟩ :=
    (isCompact_setOf_isTransportPlan p q).exists_isMinOn
      ⟨fun a b => p a * q b, productPlan_isPlan p q hp0 hp1 hq0 hq1⟩
      hcont.continuousOn
  exact ⟨π, hπ, fun π' hπ' => hmin hπ'⟩

/-! ## 五、对偶弱定理（Kantorovich 下界方向） -/

/-- **对偶弱定理**：对任意可行计划 `π` 与任意代价下界势 `(f, g)`
（即 `∀ a b, f a + g b ≤ c a b`），有
`∑ a, f a * p a + ∑ b, g b * q b ≤ transportCost c π`。

证明思路：左边 = `∑ a ∑ b, π a b * (f a + g b)`（用两组边缘约束），
再由逐项不等式 `f a + g b ≤ c a b` 与 `π a b ≥ 0` 逐项放大。 -/
theorem dual_weak (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ)
    (π : α → β → ℝ) (f : α → ℝ) (g : β → ℝ)
    (hπ : IsTransportPlan p q π) (hfg : ∀ a b, f a + g b ≤ c a b) :
    (∑ a, f a * p a) + (∑ b, g b * q b) ≤ transportCost c π := by
  have h1 : ∑ a, f a * p a = ∑ a, ∑ b, f a * π a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hπ.2.1 a, Finset.mul_sum]
  have h2 : ∑ b, g b * q b = ∑ a, ∑ b, g b * π a b := by
    calc ∑ b, g b * q b = ∑ b, ∑ a, g b * π a b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← hπ.2.2 b, Finset.mul_sum]
      _ = ∑ a, ∑ b, g b * π a b := Finset.sum_comm
  have hkey : (∑ a, f a * p a) + (∑ b, g b * q b) =
      ∑ a, ∑ b, π a b * (f a + g b) := by
    calc (∑ a, f a * p a) + (∑ b, g b * q b)
        = (∑ a, ∑ b, f a * π a b) + (∑ a, ∑ b, g b * π a b) := by rw [h1, h2]
      _ = ∑ a, ((∑ b, f a * π a b) + (∑ b, g b * π a b)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ a, ∑ b, π a b * (f a + g b) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
  rw [hkey, transportCost]
  exact Finset.sum_le_sum fun a _ =>
    Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_left (hfg a b) (hπ.1 a b)

/-- **对偶弱定理（最优计划形式）**：若 `π*` 是最优计划，
则对任意下界势 `(f, g)`，
`∑ a, f a * p a + ∑ b, g b * q b ≤ transportCost c π*`。
即对偶问题的任意可行值不超过原问题的最优值（`max_{f,g} ≤ min_π` 的一半）。 -/
theorem dual_weak_optimal (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ)
    (πstar : α → β → ℝ) (f : α → ℝ) (g : β → ℝ)
    (hπ : IsTransportPlan p q πstar)
    (_hopt : ∀ π : α → β → ℝ, IsTransportPlan p q π →
      transportCost c πstar ≤ transportCost c π)
    (hfg : ∀ a b, f a + g b ≤ c a b) :
    (∑ a, f a * p a) + (∑ b, g b * q b) ≤ transportCost c πstar :=
  dual_weak p q c πstar f g hπ hfg

/-! ## 六、最优计划的存在性（用原问题值 `otValue` 表述）

第五节给出的是"某个计划最优"的**存在形式**；本节把最小值抽成实数
`otValue p q c := sInf (代价像)`，并证它有界、被取到。这样的"值形式"是
第六节强对偶与第七节互补松弛论断的前提。 -/

/-- **原问题最优值**：`otValue p q c = inf { transportCost c π | π 是 p→q 的计划 }`。

这是 Kantorovich 原问题的值；`W1` 就是 `c = absCost n` 时的特例。 -/
def otValue (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ) : ℝ :=
  sInf (transportCost c '' {π : α → β → ℝ | IsTransportPlan p q π})

/-- 若代价 `c` 逐点非负，则 `transportCost c` 在任意可行计划上非负。 -/
theorem transportCost_nonneg_of_nonneg {p : α → ℝ} {q : β → ℝ} {c : α → β → ℝ}
    {π : α → β → ℝ} (hπ : IsTransportPlan p q π) (hc : ∀ a b, 0 ≤ c a b) :
    0 ≤ transportCost c π := by
  unfold transportCost
  exact Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hπ.1 a b) (hc a b)

/-- 非负代价下，代价像有下界 `0`。 -/
theorem bddBelow_transportCost_image (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ)
    (hc : ∀ a b, 0 ≤ c a b) :
    BddBelow (transportCost c '' {π : α → β → ℝ | IsTransportPlan p q π}) :=
  ⟨0, fun y hy => by
    rcases hy with ⟨π, hπ, rfl⟩
    exact transportCost_nonneg_of_nonneg hπ hc⟩

/-- **非负代价下任意可行计划的代价 ≥ `otValue`**（下确界的下界性质）。

**诚实标注**：需要代价逐点非负（`hc`）才能给出与 `π` 无关的下界；
没有 `hc` 时下确界可能是 `−∞` 形式（在 `ℝ` 上表现为无下界），
本条不声称那种情形。 -/
theorem otValue_le_cost {p : α → ℝ} {q : β → ℝ} {c : α → β → ℝ}
    {π : α → β → ℝ} (hπ : IsTransportPlan p q π) (hc : ∀ a b, 0 ≤ c a b) :
    otValue p q c ≤ transportCost c π := by
  have hbdd := bddBelow_transportCost_image p q c hc
  show sInf (transportCost c '' {σ : α → β → ℝ | IsTransportPlan p q σ}) ≤ transportCost c π
  exact csInf_le hbdd ⟨π, hπ, rfl⟩

/-- **最优值被取到**：概率向量 `p, q` 与非负代价 `c` 下，
存在可行计划 `π*`，其代价恰为 `otValue p q c`。
（用 `isCompact_setOf_isTransportPlan` 上的极值定理，而不是 `csInf_mem`
——后者在本版 mathlib 要求 `WellFoundedLT ℝ`，对实数不成立。）

**诚实边界**：这里只断言 `π*` 存在且达到 `otValue`；**不**给出 `π*` 的显式构造
（例如西北角法 / 单调耦合）。 -/
theorem exists_plan_attaining_otValue (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    ∃ π : α → β → ℝ, IsTransportPlan p q π ∧ transportCost c π = otValue p q c := by
  have hcont : Continuous fun π : α → β → ℝ => transportCost c π := by
    simp only [transportCost]
    exact continuous_finset_sum _ fun a _ =>
      continuous_finset_sum _ fun b _ =>
        (continuous_apply₂ a b).mul continuous_const
  obtain ⟨π, hπ, hmin⟩ :=
    (isCompact_setOf_isTransportPlan p q).exists_isMinOn
      ⟨fun a b => p a * q b, productPlan_isPlan p q hp0 hp1 hq0 hq1⟩
      hcont.continuousOn
  -- `π` 的代价是像的**下界**（`hmin` 恰恰说它是所有可行计划代价的最小值）
  have hlow : ∀ z ∈ transportCost c '' {σ : α → β → ℝ | IsTransportPlan p q σ},
      transportCost c π ≤ z := by
    rintro z ⟨ρ, hρ, hEq⟩
    rw [← hEq]
    exact hmin hρ
  have hmem : transportCost c π ∈ transportCost c ''
      {σ : α → β → ℝ | IsTransportPlan p q σ} := ⟨π, hπ, rfl⟩
  refine ⟨π, hπ, le_antisymm ?_ ?_⟩
  · -- transportCost c π ≤ otValue
    show transportCost c π ≤
      sInf (transportCost c '' {σ : α → β → ℝ | IsTransportPlan p q σ})
    exact le_csInf ⟨_, hmem⟩ hlow
  · -- otValue ≤ transportCost c π
    show sInf (transportCost c '' {σ : α → β → ℝ | IsTransportPlan p q σ})
        ≤ transportCost c π
    exact csInf_le ⟨transportCost c π, hlow⟩ hmem

/-- **`otValue` 的最优性（最优化性质）**：取到 `otValue p q c` 的可行计划确是最优的。

证明：`π*` 的代价等于 `otValue`；对任意可行 `π`，
`otValue ≤ transportCost c π`（由 `otValue_le_cost`，需代价非负）即得。 -/
theorem otValue_minimal (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1)
    (hc : ∀ a b, 0 ≤ c a b) :
    ∃ πstar : α → β → ℝ, IsTransportPlan p q πstar ∧
      transportCost c πstar = otValue p q c ∧
      ∀ π : α → β → ℝ, IsTransportPlan p q π →
        transportCost c πstar ≤ transportCost c π := by
  obtain ⟨π, hπ, hval⟩ := exists_plan_attaining_otValue p q c hp0 hp1 hq0 hq1
  exact ⟨π, hπ, hval, fun σ hσ => by
    rw [hval]
    exact otValue_le_cost hσ hc⟩

end Lattice
