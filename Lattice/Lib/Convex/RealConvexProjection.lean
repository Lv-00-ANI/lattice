import Mathlib
import Lattice.Lib.Optim.RealProjGrad
/-!
# LATTICE: 一般闭凸集的投影 —— 变分不等式路线与投影非扩张

RealProjGrad 的 `proj_nonexpansive` 只覆盖 mathlib 有完备正交投影算子的**闭子空间**
（`orthogonalProjection K`）。本文件补齐**一般闭凸集** C（实内积空间 F 的凸子集）上的
投影理论，走 mathlib 的变分不等式（variational inequality）路线：

  · `exists_norm_eq_iInf_of_complete_convex`：C 非空、完备、凸 ⟹ 每点 x 都有最近点 p ∈ C；
  · `norm_eq_iInf_iff_real_inner_le_zero`（**变分不等式刻画**，mathlib）：
      Convex ℝ C、p ∈ C ⟹ (‖x−p‖ = ⨅_{w∈C} ‖x−w‖) ↔ ∀ y ∈ C, ⟪x−p, y−p⟫ ≤ 0。

定理清单：
  1. `convex_proj_variational`：最近点 ⟹ 变分不等式；`convex_proj_of_variational` 反向；
  2. `projOn`（def）+ `projOn_mem` + `projOn_minimal`：由 `Classical.choose` 取出的
     C 上的投影函数及其成员性/极小性；`projOn_nearest`：投影比任意可行点更近；
  3. `proj_nonexpansive_of_variational`（**核心**）：两条变分不等式 ⟹ ‖p−q‖ ≤ ‖x−y‖。
     标准证明：两式相加得 ‖p−q‖² ≤ ⟪x−y, p−q⟫，再用 Cauchy–Schwarz
     （`real_inner_le_norm`）约去 ‖p−q‖；
  4. `projOn_nonexpansive`：**一般闭凸集投影非扩张**（1 + 3 立即得到，
     这正是 RealProjGrad 中标注为后续工作的结论）；
  5. `proj_unique_variational` / `projOn_unique_of_min`：最近点唯一（不依赖严格凸性，
     直接用变分不等式相加）；
  6. `proj_fixed_iff`：P_C x = x ⟺ x ∈ C；`proj_idempotent`：P_C(P_C x) = P_C x；
  7. `projOn_subspace_eq_orthogonalProjection`（**衔接**）：K 为有正交投影的子空间时，
     本文件的一般投影与 RealProjGrad 的 `orthogonalProjection` 一致。

诚实边界：
  · `projOn` 由 `Classical.choose` 定义（借 mathlib 的最近点存在性），不是 mathlib 的
    bundled 投影算子；结论不依赖选择的具体取值（最近点唯一性 `projOn_unique_of_min`）。
  · 存在性需 `IsComplete (C : Set F)`（F 完备 + C 闭时成立：`IsClosed.isComplete`）、
    `C.Nonempty` 与 `Convex ℝ C`；唯一性/非扩张只需要凸性 + 变分不等式。
  · 本文件限于实内积空间（`InnerProductSpace ℝ F`）：mathlib 的变分不等式刻画只对 ℝ
    陈述；RCLike 𝕜 的一般版本标注为后续工作。
-/

noncomputable section

namespace Lattice

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! 辅助：实内积空间里 ⟪z, z⟫ = ‖z‖²（`inner_self_eq_norm_sq` 的 ℝ 特化）。 -/

lemma real_inner_self (z : F) : ⟪z, z⟫ = ‖z‖ ^ 2 := by
  simpa using (inner_self_eq_norm_sq (𝕜 := ℝ) z)

/-! ## 一、变分不等式刻画 -/

/-- **核心引理（变分不等式）**：若 p ∈ C 是 x 在凸集 C 上的最近点，则
∀ y ∈ C，⟪x − p, y − p⟫ ≤ 0（mathlib `norm_eq_iInf_iff_real_inner_le_zero`）。 -/
theorem convex_proj_variational {C : Set F} (hconv : Convex ℝ C) {x p : F} (hp : p ∈ C)
    (hmin : ‖x - p‖ = ⨅ w : C, ‖x - w‖) :
    ∀ y ∈ C, ⟪x - p, y - p⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv hp).mp hmin

/-- 反向：变分不等式 ⟹ 最近点。与 `convex_proj_variational` 合成完整双向刻画。 -/
theorem convex_proj_of_variational {C : Set F} (hconv : Convex ℝ C) {x p : F} (hp : p ∈ C)
    (hVI : ∀ y ∈ C, ⟪x - p, y - p⟫ ≤ 0) :
    ‖x - p‖ = ⨅ w : C, ‖x - w‖ :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv hp).mpr hVI

/-! ## 二、一般闭凸集上的投影函数（选择定义） -/

/-- 到集合 C 的投影：C 非空、完备、凸时取 x 的最近点（`Classical.choose`）。 -/
def projOn (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C) (hconv : Convex ℝ C)
    (x : F) : F :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcomp hconv x)

lemma projOn_mem (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C) (hconv : Convex ℝ C)
    (x : F) : projOn C hne hcomp hconv x ∈ C :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomp hconv x)).1

lemma projOn_minimal (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C)
    (hconv : Convex ℝ C) (x : F) :
    ‖x - projOn C hne hcomp hconv x‖ = ⨅ w : C, ‖x - w‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcomp hconv x)).2

/-- 投影是 C 上的变分不等式解（`convex_proj_variational` + `projOn_minimal`）。 -/
theorem projOn_variational (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C)
    (hconv : Convex ℝ C) (x : F) :
    ∀ y ∈ C, ⟪x - projOn C hne hcomp hconv x, y - projOn C hne hcomp hconv x⟫ ≤ 0 :=
  convex_proj_variational hconv (projOn_mem C hne hcomp hconv x)
    (projOn_minimal C hne hcomp hconv x)

/-- 投影不比任意可行点更远：y ∈ C ⟹ ‖x − P_C x‖ ≤ ‖x − y‖。 -/
theorem projOn_nearest (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C)
    (hconv : Convex ℝ C) (x : F) {y : F} (hy : y ∈ C) :
    ‖x - projOn C hne hcomp hconv x‖ ≤ ‖x - y‖ := by
  rw [projOn_minimal C hne hcomp hconv x]
  exact ciInf_le (f := fun w : C => ‖x - w‖)
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ ⟨y, hy⟩

/-! ## 三、投影非扩张（核心）

两条变分不等式相加 ⟹ ‖p−q‖² ≤ ⟪x−y, p−q⟫ ≤ ‖x−y‖·‖p−q‖ ⟹ ‖p−q‖ ≤ ‖x−y‖。 -/

/-- **核心定理（投影非扩张的变分不等式形式）**：若 p、q 分别满足 x、y 在 C 上的
变分不等式，则 ‖p − q‖ ≤ ‖x − y‖。 -/
theorem proj_nonexpansive_of_variational {C : Set F} {x y p q : F}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hp : ∀ z ∈ C, ⟪x - p, z - p⟫ ≤ 0)
    (hq : ∀ z ∈ C, ⟪y - q, z - q⟫ ≤ 0) :
    ‖p - q‖ ≤ ‖x - y‖ := by
  have h1 : ⟪x - p, q - p⟫ ≤ 0 := hp q hqC
  have h2 : ⟪y - q, p - q⟫ ≤ 0 := hq p hpC
  -- 相加并把 ⟪x−p, q−p⟫ 翻成 −⟪x−p, p−q⟫
  have hsum : ⟪(y - q) - (x - p), p - q⟫ ≤ 0 := by
    rw [inner_sub_left]
    have h1' : ⟪x - p, p - q⟫ = -⟪x - p, q - p⟫ := by
      rw [show p - q = -(q - p) by abel, inner_neg_right]
    linarith
  -- (y−q) − (x−p) = (p−q) − (x−y)
  have hid : (y - q) - (x - p) = (p - q) - (x - y) := by abel
  rw [hid, inner_sub_left] at hsum
  -- ‖p−q‖² ≤ ⟪x−y, p−q⟫
  have hkey : ⟪p - q, p - q⟫ ≤ ⟪x - y, p - q⟫ := by linarith
  rw [real_inner_self] at hkey
  have hcs : ⟪x - y, p - q⟫ ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm (x - y) (p - q)
  have hmain : ‖p - q‖ ^ 2 ≤ ‖x - y‖ * ‖p - q‖ := le_trans hkey hcs
  by_cases h0 : ‖p - q‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h' : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by
      simpa [pow_two] using hmain
    exact (mul_le_mul_right hpos).mp h'

/-- **一般闭凸集的投影非扩张**：C 非空完备凸 ⟹ ‖P_C x − P_C y‖ ≤ ‖x − y‖。
（RealProjGrad 只对闭子空间证过，此处补齐一般凸集；等价于 P_C 是 1-Lipschitz。） -/
theorem projOn_nonexpansive (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C)
    (hconv : Convex ℝ C) (x y : F) :
    ‖projOn C hne hcomp hconv x - projOn C hne hcomp hconv y‖ ≤ ‖x - y‖ :=
  proj_nonexpansive_of_variational
    (projOn_mem C hne hcomp hconv x) (projOn_mem C hne hcomp hconv y)
    (projOn_variational C hne hcomp hconv x) (projOn_variational C hne hcomp hconv y)

/-! ## 四、最近点唯一性 -/

/-- 同一点 x 的两条变分不等式解相同。 -/
theorem proj_unique_variational {C : Set F} {x p q : F}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hp : ∀ z ∈ C, ⟪x - p, z - p⟫ ≤ 0)
    (hq : ∀ z ∈ C, ⟪x - q, z - q⟫ ≤ 0) : p = q := by
  have h1 : ⟪x - p, q - p⟫ ≤ 0 := hp q hqC
  have h2 : ⟪x - q, p - q⟫ ≤ 0 := hq p hpC
  have hsum : ⟪(x - p) - (x - q), q - p⟫ ≤ 0 := by
    rw [inner_sub_left]
    have h2' : ⟪x - q, q - p⟫ = -⟪x - q, p - q⟫ := by
      rw [show q - p = -(p - q) by abel, inner_neg_right]
    linarith
  have hid : (x - p) - (x - q) = q - p := by abel
  rw [hid, real_inner_self] at hsum
  have hz : ‖q - p‖ ^ 2 = 0 := le_antisymm hsum (sq_nonneg _)
  have h0 : ‖q - p‖ = 0 := sq_eq_zero_iff.mp hz
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

/-- 最近点唯一（极小性形式）：两个最近点相等（凸性 + 变分不等式）。 -/
theorem projOn_unique_of_min {C : Set F} (hconv : Convex ℝ C) {x p q : F}
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hp : ‖x - p‖ = ⨅ w : C, ‖x - w‖) (hq : ‖x - q‖ = ⨅ w : C, ‖x - w‖) : p = q :=
  proj_unique_variational hpC hqC
    (convex_proj_variational hconv hpC hp) (convex_proj_variational hconv hqC hq)

/-! ## 五、不动点与幂等 -/

/-- **不动点刻画**：P_C x = x ⟺ x ∈ C。 -/
theorem proj_fixed_iff (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C)
    (hconv : Convex ℝ C) (x : F) :
    projOn C hne hcomp hconv x = x ↔ x ∈ C := by
  constructor
  · intro h
    rw [← h]
    exact projOn_mem C hne hcomp hconv x
  · intro hx
    have hVI := projOn_variational C hne hcomp hconv x x hx
    rw [real_inner_self] at hVI
    have h0 : ‖x - projOn C hne hcomp hconv x‖ = 0 := by
      have hnn : 0 ≤ ‖x - projOn C hne hcomp hconv x‖ ^ 2 := sq_nonneg _
      have hz : ‖x - projOn C hne hcomp hconv x‖ ^ 2 = 0 := le_antisymm hVI hnn
      exact sq_eq_zero_iff.mp hz
    exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

/-- **投影幂等**：P_C(P_C x) = P_C x（P_C x ∈ C，再用 `proj_fixed_iff`）。 -/
theorem proj_idempotent (C : Set F) (hne : C.Nonempty) (hcomp : IsComplete C)
    (hconv : Convex ℝ C) (x : F) :
    projOn C hne hcomp hconv (projOn C hne hcomp hconv x) = projOn C hne hcomp hconv x :=
  (proj_fixed_iff C hne hcomp hconv (projOn C hne hcomp hconv x)).mpr
    (projOn_mem C hne hcomp hconv x)

/-! ## 六、衔接 RealProjGrad：子空间情形与正交投影一致 -/

/-- 子空间情形：若 K 有正交投影（`HasOrthogonalProjection`），则本文件的一般投影
（变分不等式路线）与 RealProjGrad 使用的 `orthogonalProjection K` 完全一致。 -/
theorem projOn_subspace_eq_orthogonalProjection (K : Submodule ℝ F) [HasOrthogonalProjection K]
    (hne : (K : Set F).Nonempty) (hcomp : IsComplete (K : Set F)) (x : F) :
    projOn (K : Set F) hne hcomp K.convex x = (orthogonalProjection K x : F) := by
  refine proj_unique_variational
    (projOn_mem (K : Set F) hne hcomp K.convex x)
    (orthogonalProjection K x).2
    (projOn_variational (K : Set F) hne hcomp K.convex x) ?_
  intro z hz
  have h1 : x - (orthogonalProjection K x : F) ∈ Kᗮ :=
    sub_orthogonalProjection_mem_orthogonal x
  have h2 : z - (orthogonalProjection K x : F) ∈ K :=
    K.sub_mem hz (orthogonalProjection K x).2
  have hzero : ⟪x - (orthogonalProjection K x : F), z - (orthogonalProjection K x : F)⟫ = 0 :=
    (Submodule.mem_orthogonal' K _).mp h1 _ h2
  rw [hzero]

/-! ## 注：闭环语义
  一般闭凸集投影（变分不等式刻画 ⟹ 投影非扩张 1-Lipschitz ⟹ 幂等 + 不动点 ⟺ 可行集），
  与 RealProjGrad 的闭子空间投影（`orthogonalProjection`；`projOn_subspace_eq_orthogonalProjection`
  表明二者一致）合成完整的约束优化投影基础：RealProjGrad 的
  `projGD_contraction_to_solution` 因而可推广到任意非空完备凸约束集 C——把
  `proj_nonexpansive` 换成 `projOn_nonexpansive`、`proj_fixed` 换成 `proj_fixed_iff` 即可，
  迭代收缩与 ε-终止（RealConvergence）结论完全不变。
  诚实边界：RCLike 𝕜（复内积空间）版本与 bundled 投影算子标注为后续工作。 -/

end Lattice
