import Mathlib
import Lattice.Lib.Lift.RealWeightedConstraints
/-!
# LATTICE: 多目标 / Pareto 最优 —— 加权标量化定理

多目标优化：n 个目标 f_i : ℝ → ℝ（i : Fin n），决策点 x : ℝ，可行集 S ⊆ ℝ。

    x Pareto 支配 y  ⟺  (∀ i, f_i x ≤ f_i y) ∧ ∃ i, f_i x < f_i y
    x 弱支配 y       ⟺  ∀ i, f_i x < f_i y
    x Pareto 最优    ⟺  x ∈ S ∧ 无 y ∈ S Pareto 支配 x
    x 弱 Pareto 最优 ⟺  x ∈ S ∧ 无 y ∈ S 弱支配 x

定理清单：
  1. `ParetoDominates` / `StrictlyDominates` / `ParetoOptimal` / `WeakParetoOptimal` /
     `WeightedSum`（def）：五个基本定义；
  2. `paretoDominates_irrefl`：支配关系非自反；
  3. `paretoDominates_trans`：支配关系传递（严格偏序）；
  4. `strictlyDominates_imp_paretoDominates`：弱支配 ⟹ Pareto 支配（需 n ≠ 0）；
  5. `weightedSum_lt_of_paretoDominates`（**核心代数引擎**）：λ > 0 且 y 支配 x
     ⟹ Σ λ_i f_i y < Σ λ_i f_i x（逐项 ≤ + 某处严格，`Finset.sum_lt_sum`）；
  6. `pareto_optimal_of_scalarization`（**加权标量化定理，核心**）：λ > 0 且 x* 是
     S 上加权和 Σ λ_i f_i 的极小者 ⟹ x* 是 Pareto 最优；
  7. `weak_pareto_optimal_of_scalarization`：λ ≥ 0、某个 λ_i > 0 且 x* 是加权
     极小者 ⟹ x* 弱 Pareto 最优（权重可含 0，结论相应减弱）；
  8. `weighted_optimal_is_pareto`：6 的重述，衔接 RealWeightedConstraints 的加权损失
     （多 term 损失 Σ w_i·L_i 的极小者即 Pareto 最优）；
  9. `pareto_no_strict_domination`：Pareto 最优 ⟹ 不存在（S 内）支配者；
 10. `weightedSum_convexOn`：凸目标的非负加权和凸（`ConvexOn.add` / `ConvexOn.smul`）；
 11. `weighted_minimizer_set_convex`：凸目标的加权极小者集凸（凸组合仍是极小者）；
 12. `pareto_from_convex`（**凸情形标量化**）：凸目标 + 凸可行集 ⟹ 加权极小者既是
     弱 Pareto 最优，其极小者集又凸。

诚实边界：
  · **逆标量化（Pareto 最优 ⟹ 存在 λ 使其为加权极小者）未证明**：经典证明需要
    目标值集凸包与原点之间的分离定理（支撑超平面）。
    ⚠ **更正（CORRECTIONS B6）**：此处早期版本写作「mathlib 4.14 无该形式的分离定理」——
    **该论断为假**：4.14 **有** `geometric_hahn_banach_closed_point` 等真分离定理
    （见 `RealSeparation.lean` docstring 7–18 行）；缺失的只是该定理到标量化的桥接。
    而**真正的原因是命题本身为假**（见 CORRECTIONS B5b），与工具无关：
    反例（有限 S）：f(x*) = (0,0)、f(y₁) = (−5,1)、
    f(y₂) = (1,−1)，x* 是 Pareto 最优，但对任意 λ ≥ 0 都有 λ·f(y₁) < 0 或
    λ·f(y₂) < 0（λ₂ ≥ 5λ₁ 与 λ₁ ≥ λ₂ 矛盾），故 x* 不是任何非负加权和的极小者。
    因此 `pareto_from_convex` 只陈述**正向**（标量化 ⟹ Pareto / 极小者集凸），
    逆向归类为后续工作。
  · 与 RealWeightedConstraints 的衔接：那里的 `weighted2_stationarity_iff` 给出加权损失的
    驻点条件（加权法方程）；本文件的定理 6/8 说明「加权损失的**极小者**（而非驻点）是
    Pareto 最优」——驻点只是必要条件，不能直接推出 Pareto 最优，这是刻意区分之处。
  · 目标个数 n = 0 时所有定义退化为平凡情形（空 ∃ 恒假），定理仍成立；
    仅在需要取出指标的引理（`strictlyDominates_imp_paretoDominates` 等）处显式假设 `NeZero n`。
-/

noncomputable section

namespace Lattice

variable {n : ℕ}

/-! ## 一、基本定义 -/

/-- **Pareto 支配**：x 支配 y ⟺ 所有目标不劣且至少一个目标严格更优。 -/
def ParetoDominates (f : Fin n → ℝ → ℝ) (x y : ℝ) : Prop :=
  (∀ i, f i x ≤ f i y) ∧ ∃ i, f i x < f i y

/-- **严格（弱）支配**：所有目标都严格更优。 -/
def StrictlyDominates (f : Fin n → ℝ → ℝ) (x y : ℝ) : Prop :=
  ∀ i, f i x < f i y

/-- **Pareto 最优**（相对可行集 S）：x ∈ S 且 S 中无点 Pareto 支配 x。 -/
def ParetoOptimal (f : Fin n → ℝ → ℝ) (S : Set ℝ) (x : ℝ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, ¬ ParetoDominates f y x

/-- **弱 Pareto 最优**：x ∈ S 且 S 中无点严格支配 x。 -/
def WeakParetoOptimal (f : Fin n → ℝ → ℝ) (S : Set ℝ) (x : ℝ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, ¬ StrictlyDominates f y x

/-- **加权和**（标量化）：Σ_i w_i · f_i x。 -/
def WeightedSum (f : Fin n → ℝ → ℝ) (w : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, w i * f i x

/-! ## 二、支配关系是严格偏序 -/

/-- 支配关系**非自反**。 -/
theorem paretoDominates_irrefl (f : Fin n → ℝ → ℝ) (x : ℝ) : ¬ ParetoDominates f x x := by
  rintro ⟨-, i, hi⟩
  exact lt_irrefl _ hi

/-- 支配关系**传递**：x 支配 y、y 支配 z ⟹ x 支配 z。
（逐项 ≤ 的传递 + 第一个严格见证直接可用。） -/
theorem paretoDominates_trans (f : Fin n → ℝ → ℝ) {x y z : ℝ}
    (hxy : ParetoDominates f x y) (hyz : ParetoDominates f y z) : ParetoDominates f x z := by
  obtain ⟨h1, i, hi⟩ := hxy
  obtain ⟨h2, -⟩ := hyz
  exact ⟨fun j => le_trans (h1 j) (h2 j), i, lt_of_lt_of_le hi (h2 i)⟩

/-- 弱支配 ⟹ Pareto 支配（需至少一个目标，即 n ≠ 0）。 -/
theorem strictlyDominates_imp_paretoDominates [NeZero n] (f : Fin n → ℝ → ℝ) {x y : ℝ}
    (h : StrictlyDominates f x y) : ParetoDominates f x y :=
  ⟨fun i => le_of_lt (h i), (0 : Fin n), h 0⟩

/-! ## 三、加权标量化的核心代数引擎 -/

/-- **核心引理**：λ > 0 且 y Pareto 支配 x ⟹ Σ λ_i f_i y < Σ λ_i f_i x。
逐项 `λ_i f_i y ≤ λ_i f_i x`，在支配的严格见证处严格（`Finset.sum_lt_sum`）。 -/
theorem weightedSum_lt_of_paretoDominates (f : Fin n → ℝ → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) {x y : ℝ} (h : ParetoDominates f y x) :
    WeightedSum f w y < WeightedSum f w x := by
  obtain ⟨hle, i0, hi0⟩ := h
  have hle' : ∀ i ∈ (Finset.univ : Finset (Fin n)), w i * f i y ≤ w i * f i x :=
    fun i _ => mul_le_mul_of_nonneg_left (hle i) (le_of_lt (hw i))
  have hlt' : ∃ i ∈ (Finset.univ : Finset (Fin n)), w i * f i y < w i * f i x :=
    ⟨i0, Finset.mem_univ i0, mul_lt_mul_of_pos_left hi0 (hw i0)⟩
  have := Finset.sum_lt_sum hle' hlt'
  simpa [WeightedSum] using this

/-- 弱支配版的代数引擎：λ ≥ 0 且某个 λ_i > 0 时，严格支配给出严格加权不等式。 -/
theorem weightedSum_lt_of_strictlyDominates (f : Fin n → ℝ → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) {x y : ℝ} (h : StrictlyDominates f y x) :
    WeightedSum f w y < WeightedSum f w x := by
  obtain ⟨i0, hi0⟩ := hpos
  have hle' : ∀ i ∈ (Finset.univ : Finset (Fin n)), w i * f i y ≤ w i * f i x :=
    fun i _ => mul_le_mul_of_nonneg_left (le_of_lt (h i)) (hw i)
  have hlt' : ∃ i ∈ (Finset.univ : Finset (Fin n)), w i * f i y < w i * f i x :=
    ⟨i0, Finset.mem_univ i0, mul_lt_mul_of_pos_left (h i0) hi0⟩
  have := Finset.sum_lt_sum hle' hlt'
  simpa [WeightedSum] using this

/-! ## 四、加权标量化定理（核心） -/

/-- **加权标量化定理**：λ > 0 且 x* 是 S 上加权和 Σ λ_i f_i 的极小者
⟹ x* 是 Pareto 最优。

证明：若 y ∈ S 支配 x*，则 `weightedSum_lt_of_paretoDominates` 给出
Σ λ f y < Σ λ f x*，与 x* 的极小性矛盾。 -/
theorem pareto_optimal_of_scalarization (f : Fin n → ℝ → ℝ) (S : Set ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) {x : ℝ} (hx : x ∈ S)
    (hmin : ∀ y ∈ S, WeightedSum f w x ≤ WeightedSum f w y) : ParetoOptimal f S x := by
  refine ⟨hx, fun y hyS hd => ?_⟩
  exact absurd (hmin y hyS) (not_le_of_gt (weightedSum_lt_of_paretoDominates f w hw hd))

/-- **弱 Pareto 版**：λ ≥ 0、存在 λ_i > 0，x* 是加权极小者 ⟹ x* 弱 Pareto 最优。
（权重允许取 0，结论相应从 Pareto 弱化为弱 Pareto。） -/
theorem weak_pareto_optimal_of_scalarization (f : Fin n → ℝ → ℝ) (S : Set ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) {x : ℝ} (hx : x ∈ S)
    (hmin : ∀ y ∈ S, WeightedSum f w x ≤ WeightedSum f w y) : WeakParetoOptimal f S x := by
  refine ⟨hx, fun y hyS hd => ?_⟩
  exact absurd (hmin y hyS) (not_le_of_gt (weightedSum_lt_of_strictlyDominates f w hw hpos hd))

/-- **加权极小者即 Pareto 最优**（`pareto_optimal_of_scalarization` 的重述，
衔接 RealWeightedConstraints 的加权损失 Σ_i w_i·L_i：多 term 损失的**极小者**
（而非仅驻点）是 Pareto 最优）。 -/
theorem weighted_optimal_is_pareto (f : Fin n → ℝ → ℝ) (S : Set ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) {x : ℝ} (hx : x ∈ S)
    (hmin : ∀ y ∈ S, WeightedSum f w x ≤ WeightedSum f w y) : ParetoOptimal f S x :=
  pareto_optimal_of_scalarization f S w hw hx hmin

/-! ## 五、Pareto 最优 ⟹ 无支配者 -/

/-- **Pareto 最优 ⟹ 不存在严格支配者**：不存在 y ∈ S Pareto 支配 x。
（这正是否定形式下的定义，单独列出以便与「支配者不存在」的直觉对齐。） -/
theorem pareto_no_strict_domination (f : Fin n → ℝ → ℝ) (S : Set ℝ) {x : ℝ}
    (hx : ParetoOptimal f S x) : ¬ ∃ y, y ∈ S ∧ ParetoDominates f y x := by
  rintro ⟨y, hyS, hd⟩
  exact hx.2 y hyS hd

/-- Pareto 最优的等价刻画：x ∈ S ∧ 不存在支配者。 -/
theorem pareto_optimal_iff (f : Fin n → ℝ → ℝ) (S : Set ℝ) (x : ℝ) :
    ParetoOptimal f S x ↔ x ∈ S ∧ ¬ ∃ y, y ∈ S ∧ ParetoDominates f y x := by
  constructor
  · intro h
    exact ⟨h.1, pareto_no_strict_domination f S h⟩
  · rintro ⟨hxS, hno⟩
    refine ⟨hxS, fun y hyS hd => hno ⟨y, hyS, hd⟩⟩

/-- Pareto 最优 ⟹ 弱 Pareto 最优（需 n ≠ 0：弱支配要求所有坐标严格，支配要求一个）。 -/
theorem paretoOptimal_imp_weak [NeZero n] (f : Fin n → ℝ → ℝ) (S : Set ℝ) {x : ℝ}
    (hx : ParetoOptimal f S x) : WeakParetoOptimal f S x :=
  ⟨hx.1, fun y hyS hs => hx.2 y hyS (strictlyDominates_imp_paretoDominates f hs)⟩

/-! ## 六、凸情形：加权和凸 + 极小者集凸 -/

/-- **凸目标的非负加权和凸**：∀i, f_i 在 S 上凸、w_i ≥ 0 ⟹ Σ w_i f_i 在 S 上凸。
证明：直接用 `ConvexOn` 的定义——逐项用凸性 `f_i(ax+by) ≤ a·f_i x + b·f_i y`，
乘以 w_i ≥ 0 后求和，再用 `Finset.sum_add_distrib` / `Finset.mul_sum` 分解。 -/
theorem weightedSum_convexOn (f : Fin n → ℝ → ℝ) (S : Set ℝ) (w : Fin n → ℝ)
    (hS : Convex ℝ S) (hconv : ∀ i, ConvexOn ℝ S (f i)) (hw : ∀ i, 0 ≤ w i) :
    ConvexOn ℝ S (WeightedSum f w) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  have hstep : ∀ i : Fin n, w i * f i (a • x + b • y) ≤ a * (w i * f i x) + b * (w i * f i y) := by
    intro i
    have h1 : w i * f i (a • x + b • y) ≤ w i * (a • f i x + b • f i y) :=
      mul_le_mul_of_nonneg_left ((hconv i).2 hx hy ha hb hab) (hw i)
    have h2 : w i * (a • f i x + b • f i y) = a * (w i * f i x) + b * (w i * f i y) := by
      rw [smul_eq_mul, smul_eq_mul]; ring
    linarith
  have hsum : ∑ i, w i * f i (a • x + b • y)
      ≤ ∑ i, (a * (w i * f i x) + b * (w i * f i y)) :=
    Finset.sum_le_sum fun i _ => hstep i
  have hsplit : ∑ i, (a * (w i * f i x) + b * (w i * f i y))
      = a * (∑ i, w i * f i x) + b * (∑ i, w i * f i y) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  calc ∑ i, w i * f i (a • x + b • y)
      ≤ ∑ i, (a * (w i * f i x) + b * (w i * f i y)) := hsum
    _ = a * (∑ i, w i * f i x) + b * (∑ i, w i * f i y) := hsplit

/-- **加权极小者集凸**：凸目标的非负加权极小者集是凸集。
证明：x、z 都是极小者时，凸组合 a•x + b•z 处加权和 ≤ a·W(x) + b·W(z) ≤ W(y)
（凸性 + 极小性 + a, b ≥ 0 且 a + b = 1）。 -/
theorem weighted_minimizer_set_convex (f : Fin n → ℝ → ℝ) (S : Set ℝ) (w : Fin n → ℝ)
    (hS : Convex ℝ S) (hconv : ∀ i, ConvexOn ℝ S (f i)) (hw : ∀ i, 0 ≤ w i) :
    Convex ℝ {x | x ∈ S ∧ ∀ y ∈ S, WeightedSum f w x ≤ WeightedSum f w y} := by
  have hW : ConvexOn ℝ S (WeightedSum f w) := weightedSum_convexOn f S w hS hconv hw
  intro x hx z hz a b ha hb hab
  obtain ⟨hxS, hxmin⟩ := hx
  obtain ⟨hzS, hzmin⟩ := hz
  refine ⟨hS hxS hzS ha hb hab, ?_⟩
  intro y hy
  have hWc := hW.2 hxS hzS ha hb hab
  have e1 : a • WeightedSum f w x ≤ a • WeightedSum f w y := by
    rw [smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hxmin y hy) ha
  have e2 : b • WeightedSum f w z ≤ b • WeightedSum f w y := by
    rw [smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hzmin y hy) hb
  have e3 : a • WeightedSum f w y + b • WeightedSum f w y = WeightedSum f w y := by
    rw [← add_smul, hab, one_smul]
  calc
    WeightedSum f w (a • x + b • z)
        ≤ a • WeightedSum f w x + b • WeightedSum f w z := hWc
    _ ≤ a • WeightedSum f w y + b • WeightedSum f w y := add_le_add e1 e2
    _ = WeightedSum f w y := e3

/-- **凸情形标量化**：凸目标 + 凸可行集、λ ≥ 0 且某个 λ_i > 0 ⟹ 加权极小者 x*
既弱 Pareto 最优，加权极小者集又是凸集。

注意这只是**正向**（标量化 ⟹ Pareto 性质）；逆向（Pareto 最优 ⟹ 是某加权和的极小者）
需要分离定理，且对离散可行集为假（见文件头反例），故未在此陈述。 -/
theorem pareto_from_convex (f : Fin n → ℝ → ℝ) (S : Set ℝ) (w : Fin n → ℝ)
    (hS : Convex ℝ S) (hconv : ∀ i, ConvexOn ℝ S (f i))
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) {x : ℝ} (hx : x ∈ S)
    (hmin : ∀ y ∈ S, WeightedSum f w x ≤ WeightedSum f w y) :
    WeakParetoOptimal f S x ∧
      Convex ℝ {z | z ∈ S ∧ ∀ y ∈ S, WeightedSum f w z ≤ WeightedSum f w y} :=
  ⟨weak_pareto_optimal_of_scalarization f S w hw hpos hx hmin,
   weighted_minimizer_set_convex f S w hS hconv hw⟩

/-! ## 注：与既有文件的关系
  · RealWeightedConstraints：加权损失 Σ_i w_i·L_i 的驻点条件（加权法方程）是极小性的
    **必要条件**；本文件的 `weighted_optimal_is_pareto` 把「极小者」（而非驻点）升级为
    Pareto 最优——省去该必要的中间步骤，直接由极小性出发。
  · RealKKT / RealDualTheory：约束问题的 KKT 点在最优点处给出，是单目标语言的；
    Pareto 语言刻画的是**多目标之间的不可比性**，两者在「标量化 + 单目标 KKT」下交汇。 -/

end Lattice
