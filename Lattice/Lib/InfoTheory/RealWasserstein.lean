import Mathlib
import Lattice.Lib.InfoTheory.RealOptimalTransport
/-!
# LATTICE: 有限支撑 1-Wasserstein 距离（一维代价 `|a - b|`）

本文件在有限支撑概率向量上形式化 1-Wasserstein 距离
`W1 p q = inf { ∑ a ∑ b, π a b * |a - b| | π 是 p 到 q 的传输计划 }`，
其中状态空间取 `Fin n`（用 `(a : ℝ)` 作为有序坐标），代价 `c a b = |(a:ℝ) - (b:ℝ)|`。

## 已真证的主结果

1. `absCost` / `W1`：代价与 1-Wasserstein 距离的定义（下确界形式）；
2. `W1_nonneg`：概率向量下 `0 ≤ W1 p q`；
3. `W1_self`：`W1 p p = 0`（用对角计划与 `le_antisymm`）；
4. `W1_comm`：`W1 p q = W1 q p`（转置双射 + `|a - b| = |b - a|`）；
5. `W1_triangle`：`W1 p r ≤ W1 p q + W1 q r`（**gluing**：把 π₁（p→q）与 π₂（q→r）
   粘成 γ(a,c) = ∑ b, π₁ a b * π₂ b c / q b，利用 `|a-c| ≤ |a-b| + |b-c|`
   与两组边缘约束 `∑ c π₂ b c = q b`、`∑ a π₁ a b = q b`）；
6. `kr_upper`（Kantorovich–Rubinstein 的 **sup ≤ W1** 方向）：对 1-Lipschitz 的
   `f : Fin n → ℝ`，`∑ a, f a * (p a - q a) ≤ W1 p q`（用 `g b = -f b` 与 OT 文件的
   `Lattice.dual_weak`，再对可行集取下确界）；
7. `kp_lipschitz_bound` 等辅助引理（1-Lipschitz 势的差分界、取负与平移封闭）；
8. `W1_le_product_cost`：乘积计划给出的上界 `W1 p q ≤ ∑ a ∑ b p a * q b * |a - b|`。

## 诚实边界（降级 / 未做，明确标注）

- **降级（标注）**：`W1_triangle` 附加假设 `hqpos : ∀ b, 0 < q b`（中间分布 `q`
  处处正）。这是由于 gluing 中的除法 `π₁ a b * π₂ b c / q b` 在 `q b = 0` 时
  需要额外的分支处理（虽然数学上成立，因为此时分子也为 0）；本文件**未做**
  `q b = 0` 的无条件下标版本，明确标注为降级。
- **未做（标注）**：`W1 ≤ sup`（即 Kantorovich–Rubinstein 的另一半，
  一般需构造最优 Kantorovich 势，例如一维离散的累积分布
  `F_i = ∑_{j ≤ i} p j`）。本文件**只证了** `kr_upper` 的 `sup ≤ W1` 方向，
  并在 `kr_upper` 的 docstring 中标注「未做另一半」。
- **未做（标注）**：一般测度空间、非有限支撑、`p ≠ 0` 但 `∑ p ≠ 1`
  （非概率测度）的 Wasserstein 距离未做。
- 全部声明无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

open scoped BigOperators

namespace Lattice.Lib.InfoTheory.RealWasserstein
variable {n : ℕ}

/-! ## 一、定义 -/

/-- 一维代价函数：`absCost n a b = |(a : ℝ) - (b : ℝ)|`，
即把 `Fin n` 看作 `n` 个有序点。 -/
def absCost (n : ℕ) : Fin n → Fin n → ℝ := fun a b => |(a : ℝ) - (b : ℝ)|

/-- **1-Wasserstein 距离**（有限支撑）：
`W1 p q` 是 `p → q` 的所有传输计划代价的下确界。 -/
def W1 (p q : Fin n → ℝ) : ℝ :=
  sInf (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π})

/-- **1-Lipschitz 势**：`f : Fin n → ℝ` 关于代价 `|(a:ℝ) - (b:ℝ)|` 是 1-Lipschitz 的。
这是 Kantorovich 对偶问题的可行条件。 -/
def IsOneLipschitz (f : Fin n → ℝ) : Prop :=
  ∀ a b, |f a - f b| ≤ |(a : ℝ) - (b : ℝ)|

/-- 对角计划：`π a b = if a = b then p a else 0`（用于 `W1_self`）。 -/
def diagonalPlan (p : Fin n → ℝ) : Fin n → Fin n → ℝ := fun a b => if a = b then p a else 0

/-! ## 二、基本引理 -/

/-- 转置：`p → q` 的传输计划转置后是 `q → p` 的传输计划。 -/
theorem transpose_isPlan {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} {q : β → ℝ} {π : α → β → ℝ} (hπ : IsTransportPlan p q π) :
    IsTransportPlan q p (fun b a => π a b) :=
  ⟨fun b a => hπ.1 a b, fun b => hπ.2.2 b, fun a => hπ.2.1 a⟩

/-- 一维代价下，传输代价在转置下不变（`∑∑` 交换 + `|a - b| = |b - a|`）。 -/
theorem transportCost_transpose (π : Fin n → Fin n → ℝ) :
    transportCost (absCost n) (fun b a => π a b) = transportCost (absCost n) π := by
  simp only [transportCost, absCost]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [abs_sub_comm]

/-- 非负代价下传输代价非负。 -/
theorem transportCost_absCost_nonneg {p q : Fin n → ℝ} {π : Fin n → Fin n → ℝ}
    (hπ : IsTransportPlan p q π) : 0 ≤ transportCost (absCost n) π := by
  simp only [transportCost, absCost]
  exact Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hπ.1 a b) (abs_nonneg _)

/-- 可行计划集（的代价像）有下界（下界取 `0`）。 -/
theorem W1_bddBelow (p q : Fin n → ℝ) :
    BddBelow (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π}) :=
  ⟨0, fun y hy => by
    rcases hy with ⟨π, hπ, rfl⟩
    exact transportCost_absCost_nonneg hπ⟩

/-- 可行计划集非空 ⟹ 其代价像非空。 -/
theorem W1_image_nonempty {p q : Fin n → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π}).Nonempty :=
  ⟨_, fun a b => p a * q b, productPlan_isPlan p q hp0 hp1 hq0 hq1, rfl⟩

/-- 可行计划集的像关于 `p, q` 交换不变（转置是双射）。 -/
theorem W1_image_comm (p q : Fin n → ℝ) :
    (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π}) =
      (transportCost (absCost n) '' {σ : Fin n → Fin n → ℝ | IsTransportPlan q p σ}) := by
  ext y
  constructor
  · rintro ⟨π, hπ, rfl⟩
    exact ⟨fun b a => π a b, transpose_isPlan hπ, transportCost_transpose π⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨fun a b => σ b a, transpose_isPlan hσ, transportCost_transpose σ⟩

/-! ## 三、对角计划与 `W1_self` -/

/-- 对角计划是传输计划（要求 `p` 非负）。 -/
theorem diagonalPlan_isPlan {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) :
    IsTransportPlan p p (diagonalPlan p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    change 0 ≤ (if a = b then p a else 0)
    by_cases hab : a = b
    · rw [if_pos hab, hab]
      exact hp0 b
    · rw [if_neg hab]
  · intro a
    change (∑ x : Fin n, (if a = x then p a else 0)) = p a
    rw [Finset.sum_ite_eq Finset.univ a (fun _ => p a)]
    simp
  · intro b
    change (∑ x : Fin n, (if x = b then p x else 0)) = p b
    rw [Finset.sum_ite_eq' Finset.univ b p]
    simp

/-- 对角计划的传输代价为 `0`（因为只有 `a = b` 的项，而 `|a - a| = 0`）。 -/
theorem diagonalPlan_cost (p : Fin n → ℝ) :
    transportCost (absCost n) (diagonalPlan p) = 0 := by
  simp only [transportCost, diagonalPlan, absCost]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · simp [hab]

/-! ## 四、度量性质 -/

/-- **非负性**：概率向量下 `0 ≤ W1 p q`（可行集非空 + 每个可行代价非负）。 -/
theorem W1_nonneg {p q : Fin n → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    0 ≤ W1 p q := by
  rw [W1]
  refine le_csInf (W1_image_nonempty hp0 hp1 hq0 hq1) ?_
  rintro y ⟨π, hπ, rfl⟩
  exact transportCost_absCost_nonneg hπ

/-- **同一性**：`W1 p p = 0`（对角计划给出 `W1 p p ≤ 0`，非负性给出反向）。 -/
theorem W1_self {p : Fin n → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    W1 p p = 0 := by
  refine le_antisymm ?_ (W1_nonneg hp0 hp1 hp0 hp1)
  have hmem : transportCost (absCost n) (diagonalPlan p) ∈
      transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p p π} :=
    ⟨diagonalPlan p, diagonalPlan_isPlan hp0, rfl⟩
  rw [W1]
  calc sInf (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p p π})
      ≤ transportCost (absCost n) (diagonalPlan p) := csInf_le (W1_bddBelow p p) hmem
    _ = 0 := diagonalPlan_cost p

/-- **对称性**：`W1 p q = W1 q p`（代价像在转置下相等 ⟹ 下确界相等）。 -/
theorem W1_comm (p q : Fin n → ℝ) : W1 p q = W1 q p := by
  unfold W1
  rw [W1_image_comm]

/-- **gluing 的代价界**（三角不等式的核心）：给定可行计划
`π₁ : p → q`、`π₂ : q → r`，粘合计划
`γ a c = ∑ b, π₁ a b * π₂ b c / q b` 是 `p → r` 的可行计划，且
`W1 p r ≤ transportCost c γ ≤ transportCost c π₁ + transportCost c π₂`。
要求 `∀ b, 0 < q b`（见文件头 docstring 的降级说明）。 -/
theorem W1_triangle_aux {p q r : Fin n → ℝ} {π₁ π₂ : Fin n → Fin n → ℝ}
    (hπ₁ : IsTransportPlan p q π₁) (hπ₂ : IsTransportPlan q r π₂)
    (hqpos : ∀ b, 0 < q b) :
    W1 p r ≤ transportCost (absCost n) π₁ + transportCost (absCost n) π₂ := by
  have hqne : ∀ b, q b ≠ 0 := fun b => ne_of_gt (hqpos b)
  -- (1) 粘合计划 γ 是 p → r 的可行计划
  have hγ1 : ∀ a c, 0 ≤ ∑ b, π₁ a b * π₂ b c / q b := by
    intro a c
    exact Finset.sum_nonneg fun b _ =>
      div_nonneg (mul_nonneg (hπ₁.1 a b) (hπ₂.1 b c)) (le_of_lt (hqpos b))
  have hγ2 : ∀ a, ∑ c, ∑ b, π₁ a b * π₂ b c / q b = p a := by
    intro a
    have hb : ∀ b, (∑ c, π₁ a b * π₂ b c / q b) = π₁ a b := by
      intro b
      have h1 : (∑ c, π₁ a b * π₂ b c / q b)
          = π₁ a b * ((∑ c, π₂ b c) / q b) := by
        rw [Finset.sum_div, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [h1, hπ₂.2.1 b, div_self (hqne b), mul_one]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => hb b]
    exact hπ₁.2.1 a
  have hγ3 : ∀ c, ∑ a, ∑ b, π₁ a b * π₂ b c / q b = r c := by
    intro c
    have hb : ∀ b, (∑ a, π₁ a b * π₂ b c / q b) = π₂ b c := by
      intro b
      have h1 : (∑ a, π₁ a b * π₂ b c / q b)
          = (∑ a, π₁ a b) * (π₂ b c / q b) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [h1, hπ₁.2.2 b, mul_div_cancel₀ _ (hqne b)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => hb b]
    exact hπ₂.2.2 c
  have hγ : IsTransportPlan p r (fun a c => ∑ b, π₁ a b * π₂ b c / q b) := ⟨hγ1, hγ2, hγ3⟩
  -- (2) 代价的三重和展开
  have hA : transportCost (absCost n) (fun a c => ∑ b, π₁ a b * π₂ b c / q b)
      = ∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(a : ℝ) - (c : ℝ)| := by
    simp only [transportCost, absCost]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Finset.sum_mul Finset.univ (fun b => π₁ a b * π₂ b x / q b) |(a : ℝ) - (x : ℝ)|
  -- (3) 逐项用三角不等式放大
  have hB : ∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(a : ℝ) - (c : ℝ)|
      ≤ ∑ a, ∑ b, ∑ c,
          (π₁ a b * π₂ b c / q b) * (|(a : ℝ) - (b : ℝ)| + |(b : ℝ) - (c : ℝ)|) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      Finset.sum_le_sum fun c _ => ?_
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg (mul_nonneg (hπ₁.1 a b) (hπ₂.1 b c)) (le_of_lt (hqpos b)))
    have := dist_triangle (a : ℝ) (b : ℝ) (c : ℝ)
    simpa [Real.dist_eq] using this
  -- (4) 拆成两项
  have hC : ∑ a, ∑ b, ∑ c,
        (π₁ a b * π₂ b c / q b) * (|(a : ℝ) - (b : ℝ)| + |(b : ℝ) - (c : ℝ)|)
      = (∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(a : ℝ) - (b : ℝ)|)
        + (∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(b : ℝ) - (c : ℝ)|) := by
    simp only [mul_add, Finset.sum_add_distrib]
  -- (5) 两项分别等于两个计划的代价
  have hE1 : ∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(a : ℝ) - (b : ℝ)|
      = transportCost (absCost n) π₁ := by
    simp only [transportCost, absCost]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h1 : (∑ c, (π₁ a b * π₂ b c / q b) * |(a : ℝ) - (b : ℝ)|)
        = (π₁ a b * |(a : ℝ) - (b : ℝ)|) * ((∑ c, π₂ b c) / q b) := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [h1, hπ₂.2.1 b, div_self (hqne b), mul_one]
  have hE2 : ∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(b : ℝ) - (c : ℝ)|
      = transportCost (absCost n) π₂ := by
    simp only [transportCost, absCost]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : (∑ a, (π₁ a b * π₂ b c / q b) * |(b : ℝ) - (c : ℝ)|)
        = (∑ a, π₁ a b) * ((π₂ b c / q b) * |(b : ℝ) - (c : ℝ)|) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h1, hπ₁.2.2 b, ← mul_assoc, mul_div_cancel₀ _ (hqne b)]
  -- (6) γ 可行 ⟹ W1 p r ≤ 其代价
  have hW : W1 p r ≤ transportCost (absCost n) (fun a c => ∑ b, π₁ a b * π₂ b c / q b) := by
    rw [W1]
    exact csInf_le (W1_bddBelow p r) ⟨_, hγ, rfl⟩
  calc W1 p r ≤ transportCost (absCost n) (fun a c => ∑ b, π₁ a b * π₂ b c / q b) := hW
    _ = ∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(a : ℝ) - (c : ℝ)| := hA
    _ ≤ ∑ a, ∑ b, ∑ c,
          (π₁ a b * π₂ b c / q b) * (|(a : ℝ) - (b : ℝ)| + |(b : ℝ) - (c : ℝ)|) := hB
    _ = (∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(a : ℝ) - (b : ℝ)|)
        + (∑ a, ∑ b, ∑ c, (π₁ a b * π₂ b c / q b) * |(b : ℝ) - (c : ℝ)|) := hC
    _ = transportCost (absCost n) π₁ + transportCost (absCost n) π₂ := by rw [hE1, hE2]

/-- **三角不等式**：`W1 p r ≤ W1 p q + W1 q r`。

由 `W1_triangle_aux` 对 `π₁`、`π₂` 分别取下确界得到：
`W1 p r - W1 q r ≤ W1 p q`，即结论。

**降级（标注）**：附加假设 `hqpos : ∀ b, 0 < q b`（中间分布处处正）；
无条件下标版本（`q b = 0` 的分支）**未做**，见文件头 docstring。 -/
theorem W1_triangle {p q r : Fin n → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1)
    (hr0 : ∀ c, 0 ≤ r c) (hr1 : ∑ c, r c = 1)
    (hqpos : ∀ b, 0 < q b) :
    W1 p r ≤ W1 p q + W1 q r := by
  have hne1 := W1_image_nonempty hp0 hp1 hq0 hq1
  have hne2 := W1_image_nonempty hq0 hq1 hr0 hr1
  have step : W1 p r - W1 q r
      ≤ sInf (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π}) := by
    refine le_csInf hne1 ?_
    rintro y ⟨π₁, hπ₁, rfl⟩
    have h2 : W1 p r - transportCost (absCost n) π₁
        ≤ sInf (transportCost (absCost n) '' {σ : Fin n → Fin n → ℝ | IsTransportPlan q r σ}) := by
      refine le_csInf hne2 ?_
      rintro z ⟨π₂, hπ₂, rfl⟩
      have := W1_triangle_aux hπ₁ hπ₂ hqpos
      linarith
    linarith [show W1 q r
        = sInf (transportCost (absCost n) '' {σ : Fin n → Fin n → ℝ | IsTransportPlan q r σ})
        from rfl]
  linarith [show W1 p q
      = sInf (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π})
      from rfl]

/-! ## 五、Kantorovich–Rubinstein（有限版） -/

/-- 1-Lipschitz 势的差分界（去掉绝对值的一侧）：`f a - f b ≤ |a - b|`。 -/
theorem kp_lipschitz_bound {f : Fin n → ℝ} (hf : IsOneLipschitz f) (a b : Fin n) :
    f a - f b ≤ |(a : ℝ) - (b : ℝ)| :=
  le_trans (le_abs_self _) (hf a b)

/-- 1-Lipschitz 势的反向差分界：`f b - f a ≤ |a - b|`。 -/
theorem kp_lipschitz_bound' {f : Fin n → ℝ} (hf : IsOneLipschitz f) (a b : Fin n) :
    f b - f a ≤ |(a : ℝ) - (b : ℝ)| := by
  have h : -(f a - f b) ≤ |f a - f b| := neg_le_abs _
  linarith [hf a b]

/-- 1-Lipschitz 在取负下封闭。 -/
theorem isOneLipschitz_neg {f : Fin n → ℝ} (hf : IsOneLipschitz f) :
    IsOneLipschitz (fun a => -f a) := by
  intro a b
  have h : -f a - -f b = -(f a - f b) := by ring
  rw [h, abs_neg]
  exact hf a b

/-- 1-Lipschitz 在加常数下封闭。 -/
theorem isOneLipschitz_add_const {f : Fin n → ℝ} (hf : IsOneLipschitz f) (k : ℝ) :
    IsOneLipschitz (fun a => f a + k) := by
  intro a b
  have h : (f a + k) - (f b + k) = f a - f b := by ring
  rw [h]
  exact hf a b

/-- **Kantorovich–Rubinstein（上界方向，即 `sup ≤ W1`）**：
对 1-Lipschitz 的 `f : Fin n → ℝ`，`∑ a, f a * (p a - q a) ≤ W1 p q`。

证明：取 `g b = -f b`，由 1-Lipschitz 有 `f a + g b = f a - f b ≤ |a - b|`，
用 OT 文件的 `dual_weak` 得对每个可行计划 `π` 的界，再对可行集取 `le_csInf`。

**未做（标注）**：反方向 `W1 p q ≤ sup_f ∑ a, f a * (p a - q a)`
（需构造最优 Kantorovich 势）本文件**未做**。 -/
theorem kr_upper {p q : Fin n → ℝ} {f : Fin n → ℝ} (hf : IsOneLipschitz f)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    ∑ a, f a * (p a - q a) ≤ W1 p q := by
  rw [W1]
  refine le_csInf (W1_image_nonempty hp0 hp1 hq0 hq1) ?_
  rintro y ⟨π, hπ, rfl⟩
  have hsplit : ∑ a, f a * (p a - q a) = (∑ a, f a * p a) - (∑ a, f a * q a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hneg : ∑ a, (-f a) * q a = -(∑ a, f a * q a) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hdw : (∑ a, f a * p a) + (∑ a, (-f a) * q a)
      ≤ transportCost (absCost n) π :=
    dual_weak p q (absCost n) π f (fun a => -f a) hπ
      (fun a b => le_trans (le_abs_self _) (hf a b))
  calc ∑ a, f a * (p a - q a)
      = (∑ a, f a * p a) - (∑ a, f a * q a) := hsplit
    _ = (∑ a, f a * p a) + (∑ a, (-f a) * q a) := by rw [hneg]; ring
    _ ≤ transportCost (absCost n) π := hdw

/-- **乘积计划上界**：`W1 p q ≤ ∑ a ∑ b, p a * q b * |a - b|`
（乘积计划可行，故其代价不小于下确界）。 -/
theorem W1_le_product_cost {p q : Fin n → ℝ}
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    W1 p q ≤ ∑ a, ∑ b, p a * q b * |(a : ℝ) - (b : ℝ)| := by
  have hmem : transportCost (absCost n) (fun a b => p a * q b) ∈
      transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π} :=
    ⟨fun a b => p a * q b, productPlan_isPlan p q hp0 hp1 hq0 hq1, rfl⟩
  have hcost : transportCost (absCost n) (fun a b => p a * q b)
      = ∑ a, ∑ b, p a * q b * |(a : ℝ) - (b : ℝ)| := by
    simp only [transportCost, absCost]
  rw [W1]
  calc sInf (transportCost (absCost n) '' {π : Fin n → Fin n → ℝ | IsTransportPlan p q π})
      ≤ transportCost (absCost n) (fun a b => p a * q b) := csInf_le (W1_bddBelow p q) hmem
    _ = ∑ a, ∑ b, p a * q b * |(a : ℝ) - (b : ℝ)| := hcost

end Lattice.Lib.InfoTheory.RealWasserstein