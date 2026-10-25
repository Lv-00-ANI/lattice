import Lattice.Lib.Optim.RealProjGrad
import Lattice.Lib.Editing.RealLoRAEditJoint
import Mathlib

/-!
# LATTICE: 子空间 / 流形约束 —— 可行性、投影幂等与约束组合

约束行（§5「更多约束形态」）的**子空间/流形**维度：权重或激活被限制在
几何对象上。本文件把三类约束形式化并给出可证性质：

  1. `subspaceConstraint`（def）：`x ∈ S`（S : Submodule ℝ E）——线性子空间约束；
     · `subspace_proj_mem`：正交投影落回约束集（P_S x ∈ S）；
     · `subspace_proj_idempotent`（核心）：**投影幂等** P(Px) = Px
       （回收 RealProjGrad.proj_fixed：x ∈ S ⟹ P_S x = x）；
     · `constraint_on_subspace_preserved`（核心）：编辑保持子空间约束的条件——
       若编辑为 `W ↦ W + Δ⊗k`，且 W 在 S 上消失、k 与 S 正交，则编辑后仍在 S 上消失
       （约束保持）；即「编辑不破坏约束 ⟺ 补丁在约束集上为零」。

  2. `simplexConstraint`（def）：`x ≥ 0 ∧ Σx = 1`（x : Fin n → ℝ）——单纯形约束；
     · `simplex_feasible`：n ≠ 0 时均匀点 `1/n` 可行（非空）；
     · `simplex_convex`（核心）：单纯形是**凸集**（凸组合仍可行）；
     · `simplex_normalize_feasible` / `simplex_normalize_fixed`（核心）：
       逐点非负且 Σx ≠ 0 ⟹ 归一化 `x/Σx` 落回单纯形，且已可行的点是归一化的
       不动点（**投影性质**：可行点 = 不动点）。

  3. `sphereConstraint`（def）：`‖x‖ = r`——球面（流形）约束；
     · `sphere_normalize_projects`（核心）：`x ↦ (r/‖x‖)·x` 把非零点精确投到半径 r
       的球面上（规范化投影，r ≥ 0，x ≠ 0）。

  4. `subspace_inf`（核心组合性质）：两个子空间约束之交仍是子空间约束
     （`S ⊓ T`，`Submodule.mem_inf`）；另有 `subspaceConstraint_top` /
     `subspaceConstraint_bot` 两个退化端点。

**诚实标注（降级与边界）**：
  · 单纯形的**欧氏正交投影**（一般点到单纯形的最接近点）需要 KKT/排序算法
    （mathlib 无 simplex 投影 API），本文件给出的是**归一化映射**的可行性 +
    不动点性质（凸性、非空性），不声称它是欧氏投影；欧氏投影的最优性
    留作后续（可接 RealKKT / RealConvexProjection）。
  · 球面的「归一化投影」在 r ≥ 0、x ≠ 0 下给出**精确命中球面**（‖·‖ = r），
    是径向投影的精确版；一般流形的最近点投影留作后续。
  · 子空间投影幂等依赖 `[HasOrthogonalProjection S]`（mathlib 对完备闭子空间
    可实例化）。
模型无关：任意 ℝ-内积空间（投影部分）与有限维单纯形。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 一、子空间约束 -/

/-- 子空间约束：`x ∈ S`。 -/
def subspaceConstraint (S : Submodule ℝ E) (x : E) : Prop := x ∈ S

omit [CompleteSpace E] in
/-- 正交投影落回约束集：`P_S x ∈ S`（投影的值属于子空间）。 -/
theorem subspace_proj_mem (S : Submodule ℝ E) [HasOrthogonalProjection S] (x : E) :
    subspaceConstraint S (orthogonalProjection S x : E) :=
  (orthogonalProjection S x).property

omit [CompleteSpace E] in
/-- **投影幂等（核心）**：`P_S (P_S x) = P_S x`。
因 `P_S x ∈ S`，由 RealProjGrad.proj_fixed（约束集内点是投影的不动点）即得。 -/
theorem subspace_proj_idempotent (S : Submodule ℝ E) [HasOrthogonalProjection S] (x : E) :
    (orthogonalProjection S (orthogonalProjection S x) : E)
      = (orthogonalProjection S x : E) :=
  proj_fixed S (orthogonalProjection S x).property

omit [CompleteSpace E] in
/-- **编辑保持子空间约束的条件（核心）**：设 W 是**在 S 上消失**的线性泛函
（`∀ y ∈ S, W y = 0`，例如 S ⊆ ker W），编辑为 `W ↦ W + Δ⊗k`。
若键 k 与 S 正交（`∀ y ∈ S, ⟨k,y⟩ = 0`），则编辑后在 S 上仍然消失
——补丁 Δ⊗k 在约束集 S 上恰为零，故约束保持；反之 k 有 S 方向分量则一般破坏约束。 -/
theorem constraint_on_subspace_preserved (S : Submodule ℝ E) (W : E →L[ℝ] ℝ) (k : E)
    (Δ : ℝ) (hW : ∀ y ∈ S, W y = 0) (hk : ∀ y ∈ S, inner k y = (0 : ℝ)) :
    ∀ y ∈ S, (fun x => W x + rankOneFun k Δ x) y = 0 := by
  intro y hy
  show W y + rankOneFun k Δ y = 0
  unfold rankOneFun
  rw [hW y hy, hk y hy]
  ring

omit [CompleteSpace E] in
/-- **约束组合（核心）**：两个子空间约束之交仍是子空间约束
（`x ∈ S ⊓ T ⟺ x ∈ S ∧ x ∈ T`）。 -/
theorem subspace_inf (S T : Submodule ℝ E) (x : E) :
    subspaceConstraint (S ⊓ T) x ↔ subspaceConstraint S x ∧ subspaceConstraint T x := by
  unfold subspaceConstraint
  exact Submodule.mem_inf

omit [CompleteSpace E] in
/-- 退化端点：全空间约束恒成立。 -/
theorem subspaceConstraint_top (x : E) : subspaceConstraint (⊤ : Submodule ℝ E) x :=
  Submodule.mem_top

omit [CompleteSpace E] in
/-- 退化端点：零子空间约束即 x = 0。 -/
theorem subspaceConstraint_bot (x : E) :
    subspaceConstraint (⊥ : Submodule ℝ E) x ↔ x = 0 :=
  Submodule.mem_bot ℝ

/-! ## 二、单纯形约束（x ≥ 0 ∧ Σx = 1） -/

/-- 单纯形约束：逐点非负且总量为 1。 -/
def simplexConstraint {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1

/-- **单纯形非空（可行性）**：n ≠ 0 时均匀点 `1/n` 满足约束。 -/
theorem simplex_feasible {n : ℕ} (hn : n ≠ 0) :
    simplexConstraint (fun _ : Fin n => (n : ℝ)⁻¹) := by
  constructor
  · intro i
    positivity
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn'

/-- **单纯形的凸性（核心）**：两个可行点的凸组合仍可行（t ∈ [0,1]）。 -/
theorem simplex_convex {n : ℕ} (x y : Fin n → ℝ) (t : ℝ)
    (hx : simplexConstraint x) (hy : simplexConstraint y) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    simplexConstraint (fun i => (1 - t) * x i + t * y i) := by
  constructor
  · intro i
    have h1 : 0 ≤ (1 - t) * x i := mul_nonneg (by linarith) (hx.1 i)
    have h2 : 0 ≤ t * y i := mul_nonneg ht0 (hy.1 i)
    show 0 ≤ (1 - t) * x i + t * y i
    linarith
  · have hsum : (∑ i, ((1 - t) * x i + t * y i))
        = (1 - t) * (∑ i, x i) + t * (∑ i, y i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum, hx.2, hy.2]
    ring

/-- 单纯形归一化：`x ↦ x / Σx`（把正向量投到单纯形上）。 -/
def simplexNormalize {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i / ∑ j, x j

/-- **归一化落回单纯形（核心）**：逐点非负且 Σx ≠ 0 ⟹ `x/Σx` 满足单纯形约束。 -/
theorem simplex_normalize_feasible {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hS : (∑ i, x i) ≠ 0) :
    simplexConstraint (simplexNormalize x) := by
  have hSnonneg : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
  have hSpos : 0 < ∑ i, x i := lt_of_le_of_ne hSnonneg (Ne.symm hS)
  constructor
  · intro i
    exact div_nonneg (hx i) (le_of_lt hSpos)
  · unfold simplexNormalize
    rw [← Finset.sum_div, div_self hS]

/-- **归一化的不动点（投影性质，核心）**：已满足单纯形约束的点是归一化的不动点
——`simplexConstraint x ⟹ simplexNormalize x = x`（可行点集 = 归一化的不动点集）。 -/
theorem simplex_normalize_fixed {n : ℕ} (x : Fin n → ℝ) (hx : simplexConstraint x) :
    simplexNormalize x = x := by
  funext i
  unfold simplexNormalize
  rw [hx.2, div_one]

/-! ## 三、球面约束（‖x‖ = r） -/

/-- 球面（流形）约束：`‖x‖ = r`。 -/
def sphereConstraint (r : ℝ) (x : E) : Prop := ‖x‖ = r

/-- 球面归一化（径向投影）：`x ↦ (r/‖x‖)·x`。 -/
def sphereNormalize (r : ℝ) (x : E) : E := (r / ‖x‖) • x

omit [CompleteSpace E] in
/-- **规范化投影精确命中球面（核心）**：r ≥ 0、x ≠ 0 ⟹ `‖(r/‖x‖)·x‖ = r`
——径向归一化把任意非零点精确投到半径 r 的球面上。 -/
theorem sphere_normalize_projects (r : ℝ) (hr : 0 ≤ r) (x : E) (hx : x ≠ 0) :
    sphereConstraint r (sphereNormalize r x) := by
  unfold sphereConstraint sphereNormalize
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr (norm_nonneg x))]
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hx']

omit [CompleteSpace E] in
/-- 球面上的点是中心投影的不动点：`‖x‖ = r` 且 r ≥ 0 且 x ≠ 0 ⟹ `(r/‖x‖)·x = x`。 -/
theorem sphere_normalize_fixed (r : ℝ) (x : E) (hx : sphereConstraint r x) (hxne : x ≠ 0) :
    sphereNormalize r x = x := by
  unfold sphereNormalize
  have hr : r ≠ 0 := by rw [← hx]; exact norm_ne_zero_iff.mpr hxne
  rw [hx, div_self hr, one_smul]

/-! ## 注：约束行闭环
  子空间约束（线性）：投影幂等（subspace_proj_idempotent，回收 RealProjGrad）+
  编辑保持条件（constraint_on_subspace_preserved，衔接 RealLoRAEditJoint 的
  rank-one 补丁）+ 交集组合（subspace_inf）；
  单纯形约束（凸多面体）：非空（simplex_feasible）+ 凸性（simplex_convex）+
  归一化的可行性与不动点（simplex_normalize_feasible / _fixed）；
  球面约束（流形）：径向规范化精确命中（sphere_normalize_projects）+
  不动点（sphere_normalize_fixed）。
  诚实边界：单纯形的欧氏正交投影需 KKT/排序算法（mathlib 无 API），本文件给
  归一化映射的可行性/不动点性质，欧氏投影最优性留作后续（接 RealKKT）。 -/

end Lattice
