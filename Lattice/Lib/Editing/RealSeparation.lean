import Mathlib
import Lattice.Lib.Convex.RealStrongDuality
/-!
# LATTICE: 凸集分离 → 支撑超平面 → 拉格朗日乘子 → 零间隙（强对偶）

**#check 结果（关键修正）**：mathlib 4.14 **有**几何 Hahn–Banach 分离定理，位于
`Mathlib/Analysis/NormedSpace/HahnBanach/Separation.lean`（实测签名）：

* `geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hx : x ∉ s) :
    ∃ f u, (∀ a ∈ s, f a < u) ∧ u < f x`
* `geometric_hahn_banach_compact_closed : Convex ℝ s → IsCompact s → Convex ℝ t →
    IsClosed t → Disjoint s t → ∃ f u v, (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b`
* `geometric_hahn_banach_point_open (ht₁ : Convex ℝ t) (ht₂ : IsOpen t) (hx : x ∉ t) :
    ∃ f, ∀ b ∈ t, f x < f b`
* `geometric_hahn_banach_point_point [T1Space E] (hxy : x ≠ y) : ∃ f, f x < f y`
* `geometric_hahn_banach_open`、`geometric_hahn_banach_open_open`、`separate_convex_open_set`、
  `iInter_halfSpaces_eq`。

因此 `RealStrongDuality.lean` docstring（41–46 行）中「mathlib 4.14 没有该形式（分离定理）」
的表述**已经过时**（本文件不改动该既有文件，仅在此登记修正并在其上补出分离层）。

**本文件内容**：

一、分离定理的 LATTICE 实例化（真分离定理的直接引用 + `E = ℝ` 标量抽取 + 有限凸包 +
    紧凸/闭凸严格分离 + 两点严格分离）：
  1. `separates_point_of_closed_convex`（闭凸集与外部点弱分离）；
  2. `separates_point_of_closed_convex_real`（`E = ℝ`：分离泛函 = 乘以非零标量 `c`，
     `c ≠ 0 ∧ (∀ a ∈ s, c·a < u) ∧ u < c·x`）；
  3. `separates_point_of_finite_convex_hull`（**有限支撑版**：`Finset` 的凸包与外部点分离，
     直接衔接 RealStrongDuality 的离散支撑设定）；
  4. `separates_compact_closed_convex`（强分离：`f < u < v < f`）；
  5. `separates_point_point`（两点严格分离）。

二、支撑超平面（由分离定理导出，不假设闭性）：
  6. `supporting_functional_of_not_mem_interior`：凸集 `s` 内点集非空、`x ∉ interior s`
     ⟹ 存在非零泛函 `f`，在 `interior s` 上 `f x < f ·`，在整个 `s` 上 `f x ≤ f ·`
     （把开集的严格分离扩张到集合本身：用 `Convex.combo_self_interior_mem_interior`
     沿线段取中点，反证）。

三、**完整强对偶（标量单约束版）**：
  7. `improvingSet` / `convex_improvingSet`：改进集 `A = {(u,v) | ∃x, g x ≤ u ∧ f x ≤ v}`
     是凸的（凸函数定义的直接验证）。
  8. `interior_improvingSet_nonempty` / `not_mem_interior_improvingSet`：`A` 有内点；
     最优值点 `(0, f x̄)` 不是 `A` 的内点（否则 `(0, f x̄ − ε/2) ∈ A` 给出可行点
     改善目标，矛盾）。
  9. **`slater_multiplier_exists`（核心）**：`f`、`g` 凸、`x̄` 可行最优、Slater
     （`∃ xs, g xs < 0`）⟹ 存在最优拉格朗日乘子 `λ ≥ 0`，`∀ x, f x̄ ≤ f x + λ g x`。
     证明路线：分离定理（经定理 6）给出支撑泛函 `φ`（写成 `φ(u,v) = a·u + b·v`）
     ⟹ `b·(f x − f x̄) + a·g x ≥ 0`；用改进方向（`u, v` 可任意大）证明 `a ≥ 0`、`b ≥ 0`；
     若 `b = 0` 则 `a > 0`（否则 `φ = 0` 与分离矛盾）且 `g ≥ 0` 处处成立，与 Slater 矛盾
     ⟹ `b > 0`；取 `λ = a/b ≥ 0` 即得。
 10. **`strong_duality_convex_slater`（核心）**：同一假设下
     `∃ λ ≥ 0, (⨅ x, f x + λ g x) = f x̄ ∧ ∀ x, f x̄ ≤ f x + λ g x`
     —— **零间隙**（对偶最优值 = 原问题最优值），其中 `⨅` 是拉格朗日函数的下确界。
     证明：乘子给出 `f x̄ ≤ ⨅ L(x,λ)`；而 ⨅ 被 `L(x̄,λ) = f x̄ + λ g x̄ ≤ f x̄` 夹住。
 11. **`slater_compact_sufficient`**：`f` 连续、可行集 `{g ≤ 0}` **紧**且非空、Slater
     ⟹ 最优值**可达**（`IsCompact.exists_isMinOn`）且**零间隙**。
     这与 `RealStrongDuality.slater_not_sufficient_discrete` 的**离散非紧致反例**形成对照：
     非紧致时 Slater 不充分。

**诚实假设与边界（重要）**：
- 本文件证明的是**标量（单变量）单约束**情形的完整强对偶。**多变量 / 多约束的
  完整 KKT 强对偶本文件未证**：它需要把改进集提升到 `ℝ^n × ℝ`、证明约束集的
  相应凸性/内点条件，并对有限约束族做分离（`Fin n` 上的对偶锥 / Farkas 引理），
  这些的 Lean 工程量大得多。本文件给出的**三步分解（分离 → 支撑超平面 → 乘子存在）**
  在标量情形是**完整闭环**的，不含任何缺口。
- 乘子存在性**不需要连续性**（凸函数在 ℝ 上的内点性质已足够）；`slater_compact_sufficient`
  额外需要 `f` 连续（用于在紧可行集上取到最小值）。
- 定理 7 的改进集**未必闭**（`(g,f)` 的像可能非闭），这正是定理 6 用**内点分离**、
  不要求闭性的原因。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Set

/-! ## 一、分离定理的实例化 -/

/-- **弱分离**：闭凸集与外部点。真分离定理 `geometric_hahn_banach_closed_point` 的
LATTICE 形式。 -/
theorem separates_point_of_closed_convex {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hsc : IsClosed s) {x : E} (hx : x ∉ s) :
    ∃ (f : E →L[ℝ] ℝ) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x :=
  geometric_hahn_banach_closed_point hs hsc hx

/-- **标量版弱分离（`E = ℝ`）**：分离泛函必为「乘以非零标量 `c`」
（`f a = c·a`）。证明：`f = f 1 • id`，故 `c = f 1`；`c = 0` 会与 `u < c·x = 0`
及 `0 < u`（取 `s` 中一点）矛盾。 -/
theorem separates_point_of_closed_convex_real {s : Set ℝ} (hs : Convex ℝ s) (hsc : IsClosed s)
    {x : ℝ} (hx : x ∉ s) :
    ∃ c u : ℝ, c ≠ 0 ∧ (∀ a ∈ s, c * a < u) ∧ u < c * x := by
  obtain ⟨f, u, hfs, hfx⟩ := geometric_hahn_banach_closed_point hs hsc hx
  have hf1 : ∀ a : ℝ, f a = f 1 * a := by
    intro a
    have h : f a = f (a • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    rw [h, map_smul, smul_eq_mul, mul_comm]
  by_cases hsne : s.Nonempty
  · obtain ⟨a0, ha0⟩ := hsne
    have hc : f 1 ≠ 0 := by
      intro h0
      have hzero : ∀ a : ℝ, f a = 0 := fun a => by rw [hf1 a, h0, zero_mul]
      have hlt := hfs a0 ha0
      rw [hzero a0] at hlt
      have hle := hfx.le
      rw [hzero x] at hle
      linarith
    exact ⟨f 1, u, hc, fun a ha => by rw [← hf1 a]; exact hfs a ha, by rw [← hf1 x]; exact hfx⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hsne
    exact ⟨1, x - 1, one_ne_zero, by simp [hsne], by linarith⟩

/-- **有限凸包分离**：`Finset ℝ` 的凸包与外部点分离（衔接 RealStrongDuality 的
离散支撑设定）。凸包有限 ⟹ 闭（`Set.Finite.isClosed_convexHull`）+ 凸。 -/
theorem separates_point_of_finite_convex_hull (s : Finset ℝ) {x : ℝ}
    (hx : x ∉ (convexHull ℝ) ((s : Set ℝ))) :
    ∃ c u : ℝ, c ≠ 0 ∧ (∀ y ∈ s, c * y < u) ∧ u < c * x := by
  have hconv : Convex ℝ ((convexHull ℝ) ((s : Set ℝ))) := convex_convexHull ℝ _
  have hclosed : IsClosed ((convexHull ℝ) ((s : Set ℝ))) :=
    Set.Finite.isClosed_convexHull s.finite_toSet
  obtain ⟨c, u, hc, h1, h2⟩ := separates_point_of_closed_convex_real hconv hclosed hx
  exact ⟨c, u, hc, fun y hy => h1 y (subset_convexHull ℝ _ (Finset.mem_coe.mpr hy)), h2⟩

/-- **强分离**：紧凸集与闭凸集（严格间隙 `f < u < v < f`）。 -/
theorem separates_compact_closed_convex {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s t : Set E} (hs : Convex ℝ s) (hsc : IsCompact s) (ht : Convex ℝ t)
    (htc : IsClosed t) (hdisj : Disjoint s t) :
    ∃ (f : E →L[ℝ] ℝ) (u v : ℝ), (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
  geometric_hahn_banach_compact_closed hs hsc ht htc hdisj

/-- **两点严格分离**。 -/
theorem separates_point_point {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T1Space E]
    {x y : E} (hxy : x ≠ y) : ∃ f : E →L[ℝ] ℝ, f x < f y :=
  geometric_hahn_banach_point_point hxy

/-! ## 二、支撑超平面（内点分离 → 集合上的支撑） -/

/-- **支撑泛函（由分离定理导出）**：凸集 `s` 的内点集非空、`x` 不在 `s` 的内部
⟹ 存在**非零**连续线性泛函 `f`，在 `interior s` 上严格被 `f x` 严格下界、
在整个 `s` 上被 `f x` 下界。

证明：`geometric_hahn_banach_point_open` 把 `x` 与 `interior s` 分离（`f x < f b`，
`b ∈ interior s`）。再把结论扩张到边界点 `y ∈ s`：若 `f y < f x`，取
`b ∈ interior s`（故 `f y < f x < f b`），令 `t = (f x − f y)/(f b − f y) ∈ (0,1)`，
由 `Convex.combo_self_interior_mem_interior` 知 `(1−t)•y + t•b ∈ interior s`，
于是 `f x < f((1−t)•y + t•b) = f x`，矛盾。 -/
theorem supporting_functional_of_not_mem_interior {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    {x : E} (hxi : x ∉ interior s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ b ∈ interior s, f x < f b) ∧ ∀ y ∈ s, f x ≤ f y := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open hs.interior isOpen_interior hxi
  have hfne : f ≠ 0 := by
    obtain ⟨b, hb⟩ := hne
    intro hzero
    rw [hzero] at hf
    simpa using hf b hb
  refine ⟨f, hfne, hf, fun y hy => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨b, hb⟩ := hne
  have hyb : f y < f b := lt_trans hlt (hf b hb)
  have hden : 0 < f b - f y := by linarith
  set t : ℝ := (f x - f y) / (f b - f y) with ht
  have ht0 : 0 < t := div_pos (by linarith) hden
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hden]
    linarith [hf b hb]
  have hcombo : (1 - t) • y + t • b ∈ interior s :=
    hs.combo_self_interior_mem_interior hy hb (by linarith) ht0 (by ring)
  have hc := hf _ hcombo
  have hval : f ((1 - t) • y + t • b) = f x := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ht]
    field_simp
    ring
  linarith

/-! ## 三、改进集与完整强对偶（标量单约束） -/

/-- **改进集**：`A = {(u,v) | ∃ x, g x ≤ u ∧ f x ≤ v}`（把约束值与目标值同时放松的点集）。 -/
def improvingSet (f g : ℝ → ℝ) : Set (ℝ × ℝ) := {p | ∃ x, g x ≤ p.1 ∧ f x ≤ p.2}

/-- **改进集是凸的**：`f`、`g` 凸 ⟹ `A` 凸（取两见证点的凸组合作新见证，逐分量用凸性）。 -/
theorem convex_improvingSet {f g : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hg : ConvexOn ℝ Set.univ g) : Convex ℝ (improvingSet f g) := by
  rw [convex_iff_forall_pos]
  rintro ⟨u₁, v₁⟩ ⟨x₁, hg₁, hf₁⟩ ⟨u₂, v₂⟩ ⟨x₂, hg₂, hf₂⟩ a b ha hb hab
  refine ⟨a * x₁ + b * x₂, ?_, ?_⟩
  · have h := hg.2 (Set.mem_univ x₁) (Set.mem_univ x₂) ha.le hb.le hab
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
    have h1 : a * g x₁ ≤ a * u₁ := mul_le_mul_of_nonneg_left (by simpa using hg₁) ha.le
    have h2 : b * g x₂ ≤ b * u₂ := mul_le_mul_of_nonneg_left (by simpa using hg₂) hb.le
    show g (a * x₁ + b * x₂) ≤ a * u₁ + b * u₂
    linarith
  · have h := hf.2 (Set.mem_univ x₁) (Set.mem_univ x₂) ha.le hb.le hab
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
    have h1 : a * f x₁ ≤ a * v₁ := mul_le_mul_of_nonneg_left (by simpa using hf₁) ha.le
    have h2 : b * f x₂ ≤ b * v₂ := mul_le_mul_of_nonneg_left (by simpa using hf₂) hb.le
    show f (a * x₁ + b * x₂) ≤ a * v₁ + b * v₂
    linarith

/-- **改进集有内点**：`(g x + 1, f x + 1)` 的一个小球整个落在 `A` 内
（以 `x` 为见证）。 -/
theorem interior_improvingSet_nonempty (f g : ℝ → ℝ) (x : ℝ) :
    (interior (improvingSet f g)).Nonempty := by
  refine ⟨(g x + 1, f x + 1), ?_⟩
  have hsub : Metric.ball ((g x + 1, f x + 1) : ℝ × ℝ) 1 ⊆ improvingSet f g := by
    rintro ⟨u, v⟩ hq
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hq
    have h1 : |u - (g x + 1)| < 1 := lt_of_le_of_lt (le_max_left _ _) hq
    have h2 : |v - (f x + 1)| < 1 := lt_of_le_of_lt (le_max_right _ _) hq
    rw [abs_lt] at h1 h2
    exact ⟨x, by linarith [h1.2], by linarith [h2.2]⟩
  exact interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self one_pos)

/-- **最优值点不是改进集的内点**：`(0, f x̄)` 若为内点，则存在 `ε > 0` 使
`(0, f x̄ − ε/2) ∈ A`，即存在可行点 `y` 满足 `f y < f x̄`，与最优性矛盾。 -/
theorem not_mem_interior_improvingSet {f g : ℝ → ℝ} {xbar : ℝ} (_hfeas : g xbar ≤ 0)
    (hopt : ∀ y, g y ≤ 0 → f xbar ≤ f y) :
    ((0 : ℝ), f xbar) ∉ interior (improvingSet f g) := by
  intro hcon
  rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hcon) with ⟨ε, hε, hball⟩
  have hdist : dist (((0 : ℝ), f xbar - ε / 2)) (((0 : ℝ), f xbar)) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have hzero : |(0 : ℝ) - 0| = 0 := by simp
    have hsecond : |(f xbar - ε / 2) - f xbar| = ε / 2 := by
      rw [show f xbar - ε / 2 - f xbar = -(ε / 2) by ring, abs_neg,
        abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    rw [hzero, hsecond, max_eq_right (by linarith : (0 : ℝ) ≤ ε / 2)]
    linarith
  have hmem : ((0 : ℝ), f xbar - ε / 2) ∈ improvingSet f g := interior_subset (hball hdist)
  obtain ⟨y, hgy, hfy⟩ := hmem
  have h := hopt y hgy
  linarith

/-- **Slater 乘子存在（核心）**：`f`、`g` 凸、`x̄` 可行最优、Slater 严格可行点存在
⟹ 存在最优乘子 `λ ≥ 0`，使 `∀ x, f x̄ ≤ f x + λ g x`。

证明路线：改进集 `A` 凸、有内点、`(0, f x̄) ∉ int A`，故由支撑泛函定理得非零
`φ : ℝ² →L[ℝ] ℝ`，`φ(0, f x̄) ≤ φ y`（`y ∈ A`）。写成 `φ(u,v) = a·u + b·v`
（`a = φ(1,0)`、`b = φ(0,1)`）。取 `y = (g x, f x) ∈ A` 得
`b(f x − f x̄) + a·g x ≥ 0`。由改进方向（`u`、`v` 可任意增大且仍在 `A`）得
`a ≥ 0`、`b ≥ 0`；`b = 0` 时 `a > 0`（否则 `φ = 0` 与 `φ ≠ 0` 矛盾）迫使
`g ≥ 0` 处处成立，与 Slater 矛盾，故 `b > 0`。取 `λ = a/b ≥ 0` 即得。 -/
theorem slater_multiplier_exists {f g : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hg : ConvexOn ℝ Set.univ g) {xbar : ℝ} (hfeas : g xbar ≤ 0)
    (hopt : ∀ y, g y ≤ 0 → f xbar ≤ f y) (hslater : ∃ xs, g xs < 0) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ x, f xbar ≤ f x + lam * g x := by
  obtain ⟨phi, hphi_ne, -, hphi_sup⟩ :=
    supporting_functional_of_not_mem_interior (convex_improvingSet hf hg)
      (interior_improvingSet_nonempty f g xbar)
      (not_mem_interior_improvingSet hfeas hopt)
  set aa : ℝ := phi (1, 0) with haa
  set bb : ℝ := phi (0, 1) with hbb
  have hphi_eq : ∀ u v : ℝ, phi (u, v) = aa * u + bb * v := by
    intro u v
    have hdecomp : ((u, v) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, haa, hbb]
    ring
  have hkey : ∀ x : ℝ, 0 ≤ bb * (f x - f xbar) + aa * g x := by
    intro x
    have hmem : (g x, f x) ∈ improvingSet f g := ⟨x, le_rfl, le_rfl⟩
    have h := hphi_sup (g x, f x) hmem
    rw [hphi_eq, hphi_eq] at h
    linarith
  have haa_nonneg : 0 ≤ aa := by
    have hmem : (max (g xbar) 0 + 1, f xbar) ∈ improvingSet f g :=
      ⟨xbar, by
        have h := le_max_left (g xbar) 0
        show g xbar ≤ max (g xbar) 0 + 1
        linarith, le_rfl⟩
    have h := hphi_sup (max (g xbar) 0 + 1, f xbar) hmem
    rw [hphi_eq, hphi_eq] at h
    have hpos : (0 : ℝ) < max (g xbar) 0 + 1 := by
      have := le_max_right (g xbar) 0; linarith
    nlinarith [h, hpos]
  have hbb_nonneg : 0 ≤ bb := by
    by_contra hneg
    push_neg at hneg
    have hbne : bb ≠ 0 := ne_of_lt hneg
    set T : ℝ := (|aa * g xbar| + 1) / (-bb) with hT
    have hTpos : 0 < T := div_pos (by positivity) (by linarith)
    have hmem : (g xbar, f xbar + T) ∈ improvingSet f g :=
      ⟨xbar, le_rfl, by show f xbar ≤ f xbar + T; linarith⟩
    have h := hphi_sup (g xbar, f xbar + T) hmem
    rw [hphi_eq, hphi_eq] at h
    have hcalc : bb * (f xbar + T) = bb * f xbar - (|aa * g xbar| + 1) := by
      have hK : bb * ((|aa * g xbar| + 1) / -bb) = -(|aa * g xbar| + 1) := by
        field_simp [hbne]
        ring
      rw [hT, mul_add, hK]
      ring
    nlinarith [h, hcalc, abs_nonneg (aa * g xbar), le_abs_self (aa * g xbar)]
  have hbb_ne : bb ≠ 0 := by
    intro hbb0
    rcases eq_or_lt_of_le haa_nonneg with haa0 | haapos
    · exfalso
      apply hphi_ne
      exact ContinuousLinearMap.ext (fun p => by
        obtain ⟨u, v⟩ := p
        rw [hphi_eq u v]
        simp [haa0.symm, hbb0])
    · obtain ⟨xs, hxs⟩ := hslater
      have hx := hkey xs
      rw [hbb0] at hx
      simp only [zero_mul, zero_add] at hx
      nlinarith
  have hbb_pos : 0 < bb := lt_of_le_of_ne hbb_nonneg (Ne.symm hbb_ne)
  refine ⟨aa / bb, div_nonneg haa_nonneg hbb_pos.le, fun x => ?_⟩
  have hx := hkey x
  have h1 : (bb * (f x - f xbar) + aa * g x) / bb
      = (f x - f xbar) + (aa / bb) * g x := by
    field_simp
    ring
  have h2 : 0 ≤ (bb * (f x - f xbar) + aa * g x) / bb := div_nonneg hx hbb_pos.le
  linarith

/-- **凸 + Slater ⟹ 零间隙（完整强对偶，标量单约束版）**：
`λ` 为定理 `slater_multiplier_exists` 给出的最优乘子时，拉格朗日函数的下确界
恰等于原问题最优值 `f x̄`，且乘子给出全局下界。

证明：乘子不等式给出 `f x̄ ≤ ⨅_x L(x,λ)`；另一方面
`⨅_x L(x,λ) ≤ L(x̄,λ) = f x̄ + λ g x̄ ≤ f x̄`（`λ ≥ 0`、`g x̄ ≤ 0`）。两侧夹紧。 -/
theorem strong_duality_convex_slater {f g : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hg : ConvexOn ℝ Set.univ g) {xbar : ℝ} (hfeas : g xbar ≤ 0)
    (hopt : ∀ y, g y ≤ 0 → f xbar ≤ f y) (hslater : ∃ xs, g xs < 0) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (⨅ x, (f x + lam * g x)) = f xbar ∧
      ∀ x, f xbar ≤ f x + lam * g x := by
  obtain ⟨lam, hlam, hmult⟩ := slater_multiplier_exists hf hg hfeas hopt hslater
  refine ⟨lam, hlam, ?_, hmult⟩
  have hle : f xbar ≤ ⨅ x, (f x + lam * g x) := le_ciInf (fun x => hmult x)
  have hbdd : BddBelow (Set.range (fun x : ℝ => f x + lam * g x)) :=
    ⟨f xbar, by rintro _ ⟨x, rfl⟩; exact hmult x⟩
  have hge : (⨅ x, (f x + lam * g x)) ≤ f xbar := by
    have h1 := ciInf_le hbdd xbar
    have h2 : f xbar + lam * g xbar ≤ f xbar := by
      have := mul_nonpos_of_nonneg_of_nonpos hlam hfeas
      linarith
    linarith
  exact le_antisymm hge hle

/-- **紧致 + Slater ⟹ 零间隙（可达性）**：`f` 连续、可行集 `{g ≤ 0}` 紧且非空、
Slater 成立 ⟹ 存在可行最优解 `x̄`，且存在 `λ ≥ 0` 使零间隙成立。
与 `RealStrongDuality.slater_not_sufficient_discrete` 的离散非紧致反例形成对照：
**紧致性是 Slater 充分性的关键补充**。 -/
theorem slater_compact_sufficient {f g : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hg : ConvexOn ℝ Set.univ g) (hcont : Continuous f)
    (hne : ({x : ℝ | g x ≤ 0}).Nonempty) (hcomp : IsCompact {x : ℝ | g x ≤ 0})
    (hslater : ∃ xs, g xs < 0) :
    ∃ xbar : ℝ, g xbar ≤ 0 ∧ ∃ lam : ℝ, 0 ≤ lam ∧
      (⨅ x, (f x + lam * g x)) = f xbar := by
  obtain ⟨xbar, hxbar_mem, hxbar_min⟩ :=
    hcomp.exists_isMinOn hne (hcont.continuousOn.mono (Set.subset_univ _))
  have hfeas : g xbar ≤ 0 := hxbar_mem
  have hopt : ∀ y, g y ≤ 0 → f xbar ≤ f y := fun y hy => hxbar_min hy
  obtain ⟨lam, hlam, hgap, -⟩ := strong_duality_convex_slater hf hg hfeas hopt hslater
  exact ⟨xbar, hfeas, lam, hlam, hgap⟩

end Lattice
