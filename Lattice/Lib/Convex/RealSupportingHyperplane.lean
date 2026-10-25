import Mathlib
import Lattice.Lib.Editing.RealSeparation
import Lattice.Lib.Convex.RealConstraintQualification
/-!
# LATTICE: 支撑超平面定理（一般形式 + 一维落地 + 有限维 ℝ^d 向量形式）

**本文件是「分离定理 → 支撑超平面」的符号包装**。`RealSeparation` 已经证明
`supporting_functional_of_not_mem_interior`：

```
Convex ℝ s → (interior s).Nonempty → x ∉ interior s →
  ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ b ∈ interior s, f x < f b) ∧ ∀ y ∈ s, f x ≤ f y
```

注意符号方向是 `f x ≤ f y`（即 `x` 是 `s` 上泛函 `f` 的**最小**值点）。要得到通常的
支撑超平面（`x₀` 是 `s` 上泛函的**最大**值点：`∀ y ∈ s, f y ≤ f x₀`），只需取
`f' = -f`（`ContinuousLinearMap.neg`），不等式整体取负即可 —— 这是零成本的直接推论。

**交付内容**：
 1. `supporting_hyperplane_of_not_mem_interior`：一般形式的支撑超平面（核心）；
 2. `supporting_functional_closure_of_not_mem_interior`：把支撑泛函的结论从 `s` 扩张到
    `closure s`（分离泛函连续，`{y | f x ≤ f y}` 闭）；
 3. `supporting_hyperplane_of_boundary_point`：把 `x₀ ∉ interior s` 换成 `x₀ ∈ frontier s`
    （边界点未必属于 `s`，例如开球，故用第 2 条的闭包版本）；
 4. `supporting_hyperplane_strict_interior`：内点严格小于支撑值（严格版本）；
 5. `supporting_hyperplane_real`：一维（`E = ℝ`）标量形式 `∃ c ≠ 0, ∀ y ∈ s, c*y ≤ c*x₀`；
 6. `continuousLinearMap_eq_dotV_finStdBasis` + `supporting_hyperplane_fin`：
    **有限维 `ℝ^d` 的向量形式** `∃ a ≠ 0, ∀ y ∈ s, dotV a y ≤ dotV a x₀`
    （衔接 Farkas / KKT：支撑超平面由向量 `a` 给出）；
 7. `supporting_hyperplane_of_finite_convexHull`：有限点集凸包上的支撑超平面。

**诚实边界（标注）**：
- **未做**：假设 `(interior s).Nonempty` 的消除。紧凸集（如 `ℝ^d` 中的球面、单纯形边界）
  没有内点，此时需要**相对内部**形式的分离（或 `geometric_hahn_banach_compact_closed`），
  本文件不处理；
- **已做（带内点假设）**：无限维中「每个边界点都有支撑超平面」的一般刻画已由第 3 条
  `supporting_hyperplane_of_boundary_point` 覆盖：该定理对**任意**拓扑向量空间 `E` 成立
  （只要求 `LocallyConvexSpace ℝ E`，无有限维限制），`x₀ ∈ frontier s` ⟹ 存在非零泛函以 `x₀`
  为 `s` 上的最大值点；**未做**的是去掉 `(interior s).Nonempty`（即相对内部形式）；
- **未做**：把 `x₀ ∈ s` 假设（第 1 条）弱化到「`x₀` 是 `s` 的边界点且 `x₀ ∈ s`」以外的情形：
  第 3 条用闭包版本覆盖了「边界点不在 `s` 内」的情形，但结论中的集合是 `s` 而非 `closure s`；
- 本文件不含任何 `sorry` / `axiom` / `admit`，所有定理均真证。
-/

noncomputable section

namespace Lattice

open Set

open scoped BigOperators

/-! ## 零、标准基与连续线性泛函的坐标表示 -/

/-- `Fin d → ℝ` 的**标准基向量** `e_j`：第 `j` 个坐标为 `1`，其余为 `0`。
用 `if` 显式展开，避免依赖 `Pi.single` 求值引理的命名/方向细节。 -/
def finStdBasisVec {d : ℕ} (j : Fin d) : Fin d → ℝ := fun k => if k = j then 1 else 0

/-- **标准基展开**：`Fin d → ℝ` 中每个向量都是标准基的线性组合，`y = ∑ j, y j • e_j`。 -/
theorem sum_finStdBasisVec_smul {d : ℕ} (y : Fin d → ℝ) :
    (∑ j : Fin d, y j • finStdBasisVec j) = y := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp [finStdBasisVec]
  · intro j _ hj
    have hkj : k ≠ j := fun h => hj h.symm
    simp [finStdBasisVec, hkj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **连续线性泛函的坐标表示**：`(Fin d → ℝ) →L[ℝ] ℝ` 上任意连续线性泛函都由
坐标内积给出，`f y = dotV a y`，其中 `a j = f e_j`（`e_j` 为标准基向量）。
这是把抽象分离定理的泛函「向量化」的关键一步，直接衔接 Farkas / KKT 的乘子形式。 -/
theorem continuousLinearMap_eq_dotV_finStdBasis {d : ℕ} (f : (Fin d → ℝ) →L[ℝ] ℝ)
    (y : Fin d → ℝ) :
    f y = dotV (fun j => f (finStdBasisVec j)) y := by
  calc f y = f (∑ j : Fin d, y j • finStdBasisVec j) := by rw [sum_finStdBasisVec_smul]
    _ = ∑ j : Fin d, y j * f (finStdBasisVec j) := by
          simp only [map_sum, map_smul, smul_eq_mul]
    _ = dotV (fun j => f (finStdBasisVec j)) y := by
          simp only [dotV]
          exact Finset.sum_congr rfl fun j _ => by ring

/-! ## 一、一般形式的支撑超平面 -/

/-- **支撑超平面（一般形式，核心）**：凸集 `s` 的内点集非空、`x₀ ∈ s` 但不是 `s` 的内点
⟹ 存在**非零**连续线性泛函 `f`，使 `x₀` 是 `s` 上 `f` 的最大值点：
`∀ y ∈ s, f y ≤ f x₀`（即超平面 `{f = f x₀}` 在 `x₀` 处支撑 `s`）。

证明：`supporting_functional_of_not_mem_interior` 给出非零 `φ`，`φ x₀ ≤ φ y`（`y ∈ s`）；
取 `f = -φ` 并整体取负（`neg_le_neg`）。 -/
theorem supporting_hyperplane_of_not_mem_interior {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hnt : x₀ ∉ interior s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x₀ := by
  obtain ⟨phi, hne0, _hstrict, hsup⟩ := supporting_functional_of_not_mem_interior hs hne hnt
  refine ⟨-phi, neg_ne_zero.mpr hne0, fun y hy => ?_⟩
  have h := hsup y hy
  simpa using neg_le_neg h

/-- **支撑泛函的闭包版本**：分离泛函 `f` 的结论「`f x₀ ≤ f ·`」可以免费扩张到 `closure s`，
因为 `{y | f x₀ ≤ f y}` 是闭集（`Ici` 的原像，`f` 连续）且包含 `s`。

这是下面边界点版本（`x₀ ∈ frontier s` 但未必 `x₀ ∈ s`）的技术基础。 -/
theorem supporting_functional_closure_of_not_mem_interior {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    {x : E} (hxi : x ∉ interior s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ b ∈ interior s, f x < f b) ∧
      ∀ y ∈ closure s, f x ≤ f y := by
  obtain ⟨f, hfne, hstrict, hsup⟩ := supporting_functional_of_not_mem_interior hs hne hxi
  refine ⟨f, hfne, hstrict, ?_⟩
  have hcl : closure s ⊆ {y : E | f x ≤ f y} :=
    closure_minimal hsup (IsClosed.preimage f.continuous isClosed_Ici)
  exact fun y hy => hcl hy

/-- **支撑超平面（边界点版本）**：`x₀` 是凸集 `s` 的边界点（`frontier s = closure s \ interior s`）
⟹ 存在非零泛函在 `s` 上以 `x₀` 为最大值点。注意 `x₀` 可以**不属于** `s`（例如 `s` 为开球、
`x₀` 在球面上），故这里用闭包版本 `supporting_functional_closure_of_not_mem_interior`
再取 `f' = -f`。 -/
theorem supporting_hyperplane_of_boundary_point {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    {x₀ : E} (hbd : x₀ ∈ frontier s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x₀ := by
  obtain ⟨f, hfne, _hstrict, hsup⟩ :=
    supporting_functional_closure_of_not_mem_interior hs hne hbd.2
  refine ⟨-f, neg_ne_zero.mpr hfne, fun y hy => ?_⟩
  have h1 : f x₀ ≤ f y := hsup y (subset_closure hy)
  simpa using neg_le_neg h1

/-- **严格版本的支撑超平面**：除了一般形式的结论外，`s` 的**内点**严格低于支撑值：
`∀ y ∈ interior s, f y < f x₀`（由 `-f` 的严格分离不等式 `neg_lt_neg` 得到）。 -/
theorem supporting_hyperplane_strict_interior {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {s : Set E} (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hnt : x₀ ∉ interior s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ y ∈ interior s, f y < f x₀) ∧ ∀ y ∈ s, f y ≤ f x₀ := by
  obtain ⟨phi, hne0, hstrict, hsup⟩ := supporting_functional_of_not_mem_interior hs hne hnt
  refine ⟨-phi, neg_ne_zero.mpr hne0, ?_, ?_⟩
  · intro y hy
    have h := hstrict y hy
    simpa using neg_lt_neg h
  · intro y hy
    have h := hsup y hy
    simpa using neg_le_neg h

/-! ## 二、一维落地（`E = ℝ`） -/

/-- **一维支撑超平面**：`s ⊆ ℝ` 凸、有内点、`x₀ ∈ s` 不是内点 ⟹ 存在非零标量 `c`，使
`∀ y ∈ s, c*y ≤ c*x₀`（即 `c` 的符号给出 `x₀` 处 `s` 的「外侧」方向）。

证明：取一般形式的泛函 `f : ℝ →L[ℝ] ℝ`，利用 `f` 的线性把它写成 `f y = f 1 * y`
（`y = y • 1`，`map_smul`，`smul_eq_mul`）；`c = f 1 ≠ 0`，否则 `f = 0` 与分离矛盾。 -/
theorem supporting_hyperplane_real {s : Set ℝ} (hs : Convex ℝ s) (hne : (interior s).Nonempty)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hnt : x₀ ∉ interior s) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ y ∈ s, c * y ≤ c * x₀ := by
  obtain ⟨f, hfne, hf⟩ := supporting_hyperplane_of_not_mem_interior hs hne hx₀ hnt
  have hf1 : ∀ a : ℝ, f a = f 1 * a := by
    intro a
    have h : f a = f (a • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    rw [h, map_smul, smul_eq_mul, mul_comm]
  have hc : f 1 ≠ 0 := by
    intro h0
    apply hfne
    refine ContinuousLinearMap.ext fun x => ?_
    rw [hf1 x, h0, zero_mul]
    simp
  exact ⟨f 1, hc, fun y hy => by rw [← hf1 y, ← hf1 x₀]; exact hf y hy⟩

/-! ## 三、有限维 `ℝ^d` 的向量形式（衔接 Farkas / KKT） -/

/-- **有限维支撑超平面（向量形式，价值最高的落地）**：`s ⊆ ℝ^d` 凸、有内点、
`x₀ ∈ s` 不是内点 ⟹ 存在**非零向量 `a`**，使 `x₀` 是 `s` 上线性函数 `y ↦ dotV a y`
的最大值点。

证明：一般形式给出非零泛函 `f`；由 `continuousLinearMap_eq_dotV_finStdBasis`
把 `f` 写成 `dotV a ·`（`a j = f e_j`）；`a = 0` 会给出 `f = 0`，与 `f ≠ 0` 矛盾。 -/
theorem supporting_hyperplane_fin {d : ℕ} {s : Set (Fin d → ℝ)} (hs : Convex ℝ s)
    (hne : (interior s).Nonempty) {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ s)
    (hnt : x₀ ∉ interior s) :
    ∃ a : Fin d → ℝ, a ≠ 0 ∧ ∀ y ∈ s, dotV a y ≤ dotV a x₀ := by
  obtain ⟨f, hfne, hf⟩ := supporting_hyperplane_of_not_mem_interior hs hne hx₀ hnt
  refine ⟨fun j => f (finStdBasisVec j), ?_, ?_⟩
  · intro ha
    apply hfne
    ext y
    rw [continuousLinearMap_eq_dotV_finStdBasis f y, ha]
    simp [dotV]
  · intro y hy
    rw [← continuousLinearMap_eq_dotV_finStdBasis f y,
      ← continuousLinearMap_eq_dotV_finStdBasis f x₀]
    exact hf y hy

/-- **有限点集凸包上的支撑超平面**：`t : Finset E` 的凸包（凸、且有限 ⟹ 闭，
`Set.Finite.isClosed_convexHull`，但本定理并不需要闭性）在非内点 `x₀` 处有支撑超平面。
**诚实标注**：本定理直接调用一般形式，只登记「有限凸包」这一实例；在 `d ≥ 2` 的 `ℝ^d` 中
有限点集的凸包**没有内点**，故假设 `(interior ·).Nonempty` 在该情形下不可满足（该假设的
消除是**未做**的，见文件头 docstring）。 -/
theorem supporting_hyperplane_of_finite_convexHull {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (t : Finset E)
    (hne : (interior (convexHull ℝ ((t : Set E)))).Nonempty)
    {x₀ : E} (hx₀ : x₀ ∈ convexHull ℝ ((t : Set E)))
    (hnt : x₀ ∉ interior (convexHull ℝ ((t : Set E)))) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ convexHull ℝ ((t : Set E)), f y ≤ f x₀ :=
  supporting_hyperplane_of_not_mem_interior (convex_convexHull ℝ ((t : Set E))) hne hx₀ hnt

end Lattice
