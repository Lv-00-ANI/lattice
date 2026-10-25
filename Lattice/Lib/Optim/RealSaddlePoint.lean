import Mathlib
import Lattice.Lib.Convex.RealKKTSecondOrder
/-!
# LATTICE: 鞍点分类 —— 一维二阶判别、凸性排除鞍点与下降方向

RealKKTSecondOrder 给出「f''>0 且 f'=0 ⟹ 严格局部极小」的充分条件与 f''≥0 的必要条件。
本文件补上**分类**的另一半与鞍点概念：

   1. `IsStrictLocalMax`（def）：严格局部极大（与 `RealKKTSecondOrder.IsStrictLocalMin` 对偶）；
      `isStrictLocalMax_iff_neg`：f 在 x 严格局部极大 ⟺ −f 在 x 严格局部极小；
      `IsStrictLocalMax.toIsLocalMax`；
   2. `strict_local_max_of_deriv_sign`（**MVT 引擎的对偶**）：导数在 x 左右异号（左正右负）
      ⟹ 严格局部极大（由 RealKKTSecondOrder 的极小引擎作用于 −f 得到，
      用 `deriv.neg`）；
   3. `second_order_sufficient_max`：f''<0 于邻域、f'(x)=0 ⟹ 严格局部极大；
   4. `saddle_classification`（**分类定理**）：在 x 的 δ-邻域上 f 连续可微、f' 连续、
      f'(x)=0 时，
         · f'' 在邻域上恒正 ⟹ 严格局部极小；
         · f'' 在邻域上恒负 ⟹ 严格局部极大；
      即**二阶导数的符号决定极值类型，f''=0 时二阶信息不足**；
   5. `exists_box_of_continuousAt_pos` / `saddle_second_deriv_zero`：
      若 f'' 在 x 处连续且 x 是鞍点，则 f''(x) = 0（否则落入 4 的某一分支）；
   6. `second_deriv_zero_undetermined`（**f''=0 不可判定**）：给出两个函数
      （x⁴ 与 −x⁴），f'(0) = f''(0) = 0，一个在 0 处严格局部极小、另一个严格局部极大；
   7. `IsSaddle`（def）与 `isSaddle_cube`：x³ 在 0 处是**真鞍点**
      （驻点，但既非局部极小也非局部极大）；
   8. `convex_stationary_is_global_min` / `no_saddle_in_convex`（**凸性排除鞍点**）：
      凸函数的驻点是**全局最小点**，故不可能是鞍点；
   9. `gradient_avoidance` / `descent_direction_exists`（**下降方向/逃逸方向**）：
      `∇f(x) ≠ 0` 时存在方向 v 使一阶方向导数 `< 0`（逃逸方向），
      并给出沿该方向函数值确实下降（衔接 RealGradDescent 的梯度下降动机）。

诚实边界：
  · 一维情形。多维鞍点（Hessian 不定 ⟹ 存在正、负曲率方向）需要 Hessian 的
    形式化，属 RealHessian 的范围；本文件的 `IsSaddle` 采用**一维的标准定义**
    （驻点但既非局部极小也非局部极大），它与「Hessian 不定」在一维等价于
    「二阶信息不足（f''(x)=0）」，见 `saddle_second_deriv_zero`；
  · `saddle_classification` 的 min/max 分支以**邻域上的符号条件**表述（而非仅在 x
    处的点条件）：点条件到邻域条件需要 f'' 的连续性，`saddle_second_deriv_zero`
    正是用这一点把「鞍点」逼到 f''(x) = 0；这与 RealKKTSecondOrder 的诚实边界一致；
  · `descent_direction_exists` 只给出**一阶**下降（∃t>0, f(x+tv) < f(x)）所需的
    方向，并显式假设 `HasDerivAt f g x`；不声称全局下降或收敛率；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Lattice

/-! ## 〇、鞍点定义（先于使用给出） -/

/-- **一维鞍点**：驻点，但既不是局部极小也不是局部极大
（「二阶信息不足」的驻点；一维情形下等价于 `f''(x) = 0` 且信息不足）。 -/
def IsSaddle (f : ℝ → ℝ) (x : ℝ) : Prop :=
  deriv f x = 0 ∧ ¬ IsLocalMin f x ∧ ¬ IsLocalMax f x

/-! ## 一、严格局部极大与对偶 -/

/-- **严格局部极大**：存在 δ > 0，使 x 的 δ-邻域内所有 y ≠ x 满足 f(y) < f(x)。 -/
def IsStrictLocalMax (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ y, y ≠ x → |y - x| < δ → f y < f x

/-- **对偶**：f 在 x 严格局部极大 ⟺ `−f` 在 x 严格局部极小。 -/
theorem isStrictLocalMax_iff_neg (f : ℝ → ℝ) (x : ℝ) :
    IsStrictLocalMax f x ↔ IsStrictLocalMin (fun y : ℝ => -f y) x := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy hlt => ?_⟩
    have := h y hy hlt
    simp only []
    linarith
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun y hy hlt => ?_⟩
    have := h y hy hlt
    simp only [] at this
    linarith

/-- 严格局部极大 ⟹ 局部极大。 -/
theorem IsStrictLocalMax.toIsLocalMax {f : ℝ → ℝ} {x : ℝ} (h : IsStrictLocalMax f x) :
    IsLocalMax f x := by
  have hmin := (isStrictLocalMax_iff_neg f x).mp h
  have hmax := hmin.toIsLocalMin.neg
  simpa using hmax

/-! ## 二、MVT 引擎的对偶：导数左正右负 ⟹ 严格局部极大 -/

/-- **MVT 引擎（极大版）**：f 在 (x−η, x+η) 上连续可微，且 ∀z ≠ x，
`(z−x)·f'(z) < 0`（左正右负），则 x 是严格局部极大。

证明：`−f` 的导数满足极小引擎的异号条件（`deriv.neg`），
故 `−f` 在 x 严格局部极小，即 f 在 x 严格局部极大。 -/
theorem strict_local_max_of_deriv_sign (f : ℝ → ℝ) (x η : ℝ) (hη : 0 < η)
    (hf_cont : ContinuousOn f (Ioo (x - η) (x + η)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - η) (x + η)))
    (hsign : ∀ z ∈ Ioo (x - η) (x + η), z ≠ x → (z - x) * deriv f z < 0) :
    ∀ y, y ≠ x → |y - x| < η → f y < f x := by
  have hmin := strict_local_min_of_deriv_sign (fun y : ℝ => -f y) x η hη
    hf_cont.neg hf_diff.neg (by
      intro z hz hzx
      have hz' := hsign z hz hzx
      rw [deriv.neg]
      nlinarith)
  intro y hy hlt
  have := hmin y hy hlt
  simpa using this

/-! ## 三、二阶充分条件（极大） -/

/-- **二阶充分条件（极大）**：f 在 (x−δ, x+δ) 上连续、可微、f' 连续、f'' 处处为负，
且 f'(x) = 0，则 x 是**严格局部极大**。 -/
theorem second_order_sufficient_max (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hf_cont : ContinuousOn f (Ioo (x - δ) (x + δ)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - δ) (x + δ)))
    (hf'_cont : ContinuousOn (deriv f) (Ioo (x - δ) (x + δ)))
    (hf''_neg : ∀ z ∈ Ioo (x - δ) (x + δ), deriv (deriv f) z < 0)
    (hstat : deriv f x = 0) : IsStrictLocalMax f x := by
  have hf'neg : ContinuousOn (deriv (fun y : ℝ => -f y)) (Ioo (x - δ) (x + δ)) := by
    have h : deriv (fun y : ℝ => -f y) = fun y : ℝ => -deriv f y := by
      funext y
      exact deriv.neg
    rw [h]
    exact hf'_cont.neg
  have hf''pos : ∀ z ∈ Ioo (x - δ) (x + δ), 0 < deriv (deriv (fun y : ℝ => -f y)) z := by
    intro z hz
    have h : deriv (fun y : ℝ => -f y) = fun y : ℝ => -deriv f y := by
      funext y
      exact deriv.neg
    have h2 : deriv (deriv (fun y : ℝ => -f y)) z = -deriv (deriv f) z := by
      rw [h]
      exact deriv.neg
    rw [h2]
    have := hf''_neg z hz
    linarith
  have hstat' : deriv (fun y : ℝ => -f y) x = 0 := by
    rw [deriv.neg, hstat]
    ring
  exact (isStrictLocalMax_iff_neg f x).mpr
    (second_order_sufficient (fun y : ℝ => -f y) x δ hδ hf_cont.neg hf_diff.neg
      hf'neg hf''pos hstat')

/-! ## 四、鞍点分类 -/

/-- **鞍点分类（一维）**：在 (x−δ, x+δ) 上 f 连续可微、f' 连续、且 f'(x) = 0 时，
f'' 在该邻域上**恒正** ⟹ 严格局部极小；f'' **恒负** ⟹ 严格局部极大。
即二阶导数的符号决定极值类型。 -/
theorem saddle_classification (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hf_cont : ContinuousOn f (Ioo (x - δ) (x + δ)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - δ) (x + δ)))
    (hf'_cont : ContinuousOn (deriv f) (Ioo (x - δ) (x + δ)))
    (hstat : deriv f x = 0) :
    ((∀ z ∈ Ioo (x - δ) (x + δ), 0 < deriv (deriv f) z) → IsStrictLocalMin f x) ∧
    ((∀ z ∈ Ioo (x - δ) (x + δ), deriv (deriv f) z < 0) → IsStrictLocalMax f x) :=
  ⟨fun h => second_order_sufficient f x δ hδ hf_cont hf_diff hf'_cont h hstat,
   fun h => second_order_sufficient_max f x δ hδ hf_cont hf_diff hf'_cont h hstat⟩

/-- g 在 x 处连续且 `g x > 0` ⟹ 存在充分小的盒子使 g 在盒内严格为正
（`RealKKTSecondOrder.exists_box_of_continuousAt_neg` 的对偶）。 -/
theorem exists_box_of_continuousAt_pos (g : ℝ → ℝ) {x δ : ℝ} (hδ : 0 < δ)
    (hg : ContinuousAt g x) (hpos : 0 < g x) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∀ z, |z - x| < η → 0 < g z := by
  obtain ⟨η, hη, hηδ, hbox⟩ :=
    exists_box_of_continuousAt_neg (fun z : ℝ => -g z) hδ hg.neg (by change -g x < 0; linarith)
  refine ⟨η, hη, hηδ, fun z hz => ?_⟩
  have h' : -g z < 0 := hbox z hz
  linarith

/-- **鞍点的二阶必要条件**：f'' 在 x 处连续、x 是鞍点（驻点但既非局部极小也非局部极大）
⟹ `f''(x) = 0`；否则由分类定理落入极小或极大分支。

证明（反证）：若 f''(x) > 0，由 `exists_box_of_continuousAt_pos` 取 η ≤ δ 使 f'' > 0 于
(x−η, x+η)，由 `saddle_classification` 得严格局部极小，从而局部极小，与鞍点的
`¬IsLocalMin` 矛盾；f''(x) < 0 对称（用 `exists_box_of_continuousAt_neg`）。 -/
theorem saddle_second_deriv_zero (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hf_cont : ContinuousOn f (Ioo (x - δ) (x + δ)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - δ) (x + δ)))
    (hf'_cont : ContinuousOn (deriv f) (Ioo (x - δ) (x + δ)))
    (hf''_cont : ContinuousAt (deriv (deriv f)) x)
    (hsaddle : IsSaddle f x) : deriv (deriv f) x = 0 := by
  have hstat : deriv f x = 0 := hsaddle.1
  rcases lt_trichotomy (deriv (deriv f) x) 0 with hlt | heq | hgt
  · obtain ⟨η, hη, hηδ, hbox⟩ :=
      exists_box_of_continuousAt_neg (deriv (deriv f)) hδ hf''_cont hlt
    have hsub : Ioo (x - η) (x + η) ⊆ Ioo (x - δ) (x + δ) := by
      intro t ht
      rw [mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2, hηδ]
    have hmax : IsStrictLocalMax f x :=
      second_order_sufficient_max f x η hη (hf_cont.mono hsub) (hf_diff.mono hsub)
        (hf'_cont.mono hsub) (fun z hz => hbox z (by
          rw [abs_lt]
          constructor <;> linarith [hz.1, hz.2])) hstat
    exact absurd hmax.toIsLocalMax hsaddle.2.2
  · exact heq
  · obtain ⟨η, hη, hηδ, hbox⟩ :=
      exists_box_of_continuousAt_pos (deriv (deriv f)) hδ hf''_cont hgt
    have hsub : Ioo (x - η) (x + η) ⊆ Ioo (x - δ) (x + δ) := by
      intro t ht
      rw [mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2, hηδ]
    have hmin : IsStrictLocalMin f x :=
      second_order_sufficient f x η hη (hf_cont.mono hsub) (hf_diff.mono hsub)
        (hf'_cont.mono hsub) (fun z hz => hbox z (by
          rw [abs_lt]
          constructor <;> linarith [hz.1, hz.2])) hstat
    exact absurd hmin.toIsLocalMin hsaddle.2.1

/-! ## 五、f'' = 0 时二阶信息不足：x⁴ 与 −x⁴ -/

/-- `deriv (·⁴) x = 4x³`。 -/
lemma deriv_pow4 (x : ℝ) : deriv (fun y : ℝ => y ^ 4) x = 4 * x ^ 3 := by
  have h : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  exact h.deriv

/-- `deriv (4·(·)³) x = 12x²`。 -/
lemma deriv_four_pow3 (x : ℝ) : deriv (fun y : ℝ => 4 * y ^ 3) x = 12 * x ^ 2 := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_id x).pow 3
  have h2 := h1.const_mul (4 : ℝ)
  have := h2.deriv
  rw [this]
  ring

/-- x⁴ 在 0 处是严格局部极小。 -/
lemma isStrictLocalMin_pow4 : IsStrictLocalMin (fun x : ℝ => x ^ 4) 0 := by
  refine ⟨1, one_pos, fun y hy _ => ?_⟩
  have h2 : 0 < y ^ 2 := by
    have : y ≠ 0 := hy
    positivity
  have h4 : (0 : ℝ) < y ^ 4 := by
    have := sq_pos_of_ne_zero (ne_of_gt h2)
    nlinarith [this]
  simpa using h4

/-- −x⁴ 在 0 处是严格局部极大。 -/
lemma isStrictLocalMax_neg_pow4 : IsStrictLocalMax (fun x : ℝ => -(x ^ 4)) 0 := by
  refine (isStrictLocalMax_iff_neg (fun x : ℝ => -(x ^ 4)) 0).mpr ?_
  have h : (fun y : ℝ => -(fun x : ℝ => -(x ^ 4)) y) = fun y : ℝ => y ^ 4 := by
    funext y
    ring
  rw [h]
  exact isStrictLocalMin_pow4

/-- **f'' = 0 时二阶条件不足**：存在 f 使 f'(0) = f''(0) = 0 且 0 是严格局部极小
（f = x⁴），也存在这样的 f 使 0 是严格局部极大（f = −x⁴）。 -/
theorem second_deriv_zero_undetermined :
    (∃ f : ℝ → ℝ, deriv f 0 = 0 ∧ deriv (deriv f) 0 = 0 ∧ IsStrictLocalMin f 0) ∧
    (∃ f : ℝ → ℝ, deriv f 0 = 0 ∧ deriv (deriv f) 0 = 0 ∧ IsStrictLocalMax f 0) := by
  constructor
  · refine ⟨fun x : ℝ => x ^ 4, ?_, ?_, isStrictLocalMin_pow4⟩
    · rw [deriv_pow4]; ring
    · have h : deriv (fun x : ℝ => x ^ 4) = fun y : ℝ => 4 * y ^ 3 := by
        funext y
        exact deriv_pow4 y
      rw [h, deriv_four_pow3]
      ring
  · refine ⟨fun x : ℝ => -(x ^ 4), ?_, ?_, isStrictLocalMax_neg_pow4⟩
    · have h : deriv (fun y : ℝ => -(y ^ 4)) 0 = -deriv (fun y : ℝ => y ^ 4) 0 := deriv.neg
      rw [h, deriv_pow4]
      ring
    · have h1 : deriv (fun y : ℝ => -(y ^ 4)) = fun y : ℝ => -(4 * y ^ 3) := by
        funext y
        have := deriv.neg (f := fun y : ℝ => y ^ 4) (x := y)
        rw [this, deriv_pow4]
      rw [h1]
      have h2 : deriv (fun y : ℝ => -(4 * y ^ 3)) 0 = -deriv (fun y : ℝ => 4 * y ^ 3) 0 :=
        deriv.neg
      rw [h2, deriv_four_pow3]
      ring

/-! ## 六、真鞍点：x³ 在 0 处（`IsSaddle` 已在第〇节定义） -/

/-- `deriv (·³) x = 3x²`。 -/
lemma deriv_pow3 (x : ℝ) : deriv (fun y : ℝ => y ^ 3) x = 3 * x ^ 2 := by
  have h : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_id x).pow 3
  exact h.deriv

/-- **x³ 在 0 处是真鞍点**：`deriv = 0`，但 y < 0 时 y³ < 0（非极小）、
y > 0 时 y³ > 0（非极大）。 -/
theorem isSaddle_cube : IsSaddle (fun x : ℝ => x ^ 3) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [deriv_pow3]
    ring
  · intro hmin
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmin
    set y : ℝ := -ε / 2 with hy
    have hyball : y ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : y - 0 = -ε / 2 := by rw [hy]; ring
      rw [h1, abs_of_neg (by linarith)]
      linarith
    have hy3 : y ^ 3 < 0 := by
      have hneg : y < 0 := by rw [hy]; linarith
      have hy2 : 0 < y ^ 2 := by
        have : y ≠ 0 := ne_of_lt hneg
        positivity
      nlinarith [mul_neg_of_neg_of_pos hneg hy2]
    have hle := hsub hyball
    have hle' : (0 : ℝ) ≤ y ^ 3 := by simpa using hle
    linarith
  · intro hmax
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmax
    set y : ℝ := ε / 2 with hy
    have hyball : y ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : y - 0 = ε / 2 := by rw [hy]; ring
      rw [h1, abs_of_pos (by linarith)]
      linarith
    have hy3 : 0 < y ^ 3 := by
      have hpos : 0 < y := by rw [hy]; linarith
      have hy2 : 0 < y ^ 2 := by positivity
      nlinarith [mul_pos hpos hy2]
    have hle := hsub hyball
    have hle' : y ^ 3 ≤ (0 : ℝ) := by simpa using hle
    linarith

/-! ## 七、凸性排除鞍点 -/

/-- **凸函数的驻点是全局最小点**：`ConvexOn ℝ univ f`、f 在 x 处可导、`f'(x) = 0`
⟹ `∀ y, f x ≤ f y`。

证明：由凸性，割线斜率在 x 两侧夹住导数（`slope_le_deriv` / `deriv_le_slope`），
导数 = 0 即得两侧的差商都非负。 -/
theorem convex_stationary_is_global_min {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    {x : ℝ} (hdiff : DifferentiableAt ℝ f x) (hstat : deriv f x = 0) :
    ∀ y : ℝ, f x ≤ f y := by
  intro y
  rcases lt_trichotomy y x with hlt | heq | hgt
  · have hslope := ConvexOn.slope_le_deriv hconv (Set.mem_univ y) (Set.mem_univ x) hlt hdiff
    rw [slope_def_field] at hslope
    rw [hstat] at hslope
    have hpos : 0 < x - y := by linarith
    have : f x - f y ≤ 0 := by
      by_contra h
      push_neg at h
      have := div_pos h hpos
      linarith
    linarith
  · rw [heq]
  · have hslope := ConvexOn.deriv_le_slope hconv (Set.mem_univ x) (Set.mem_univ y) hgt hdiff
    rw [slope_def_field] at hslope
    rw [hstat] at hslope
    have hpos : 0 < y - x := by linarith
    have : 0 ≤ f y - f x := by
      by_contra h
      push_neg at h
      have := div_neg_of_neg_of_pos h hpos
      linarith
    linarith

/-- **凸函数没有鞍点**：凸函数的驻点（f 在 x 处可导）是全局最小点，
从而不可能是鞍点。 -/
theorem no_saddle_in_convex {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) {x : ℝ}
    (hdiff : DifferentiableAt ℝ f x) (hstat : deriv f x = 0) : ¬ IsSaddle f x := by
  intro hs
  have hminOn : IsMinOn f Set.univ x :=
    fun y _ => convex_stationary_is_global_min hconv hdiff hstat y
  exact hs.2.1 (IsMinOn.isLocalMin hminOn Filter.univ_mem)

/-! ## 八、下降/逃逸方向 -/

/-- **逃逸方向（代数形式）**：`g ≠ 0` 时存在方向 v 使 `g·v < 0`
（取 `v = −g`，则 `g·(−g) = −g² < 0`）。 -/
theorem gradient_avoidance (g : ℝ) (h : g ≠ 0) : ∃ v : ℝ, g * v < 0 := by
  refine ⟨-g, ?_⟩
  nlinarith [sq_pos_of_ne_zero h]

/-- **梯度下降方向的存在性**：f 在 x 处可导、`∇f(x) ≠ 0` ⟹ 存在方向 v 与 t > 0 使
`f (x + t·v) < f x`（沿 `v = −∇f(x)` 的局部下降）。
这是 RealGradDescent 中梯度下降步「确实下降」的一阶依据。 -/
theorem descent_direction_exists {f : ℝ → ℝ} {x gx : ℝ} (hd : HasDerivAt f gx x)
    (hne : gx ≠ 0) : ∃ v t : ℝ, 0 < t ∧ f (x + t * v) < f x := by
  have hneg : gx * (-gx) < 0 := by nlinarith [sq_pos_of_ne_zero hne]
  -- 路径 φ(t) = f(x + t·(−gx)) 在 0 处的导数 = gx·(−gx) < 0
  have hpath : HasDerivAt (fun t : ℝ => f (x + t * (-gx))) (gx * (-gx)) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => t * (-gx)) (-gx) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (-gx)
    have h2 : HasDerivAt (fun t : ℝ => x + t * (-gx)) (-gx) 0 := hinner.const_add x
    have hd' : HasDerivAt f gx ((fun t : ℝ => x + t * (-gx)) 0) := by
      have h0 : (fun t : ℝ => x + t * (-gx)) 0 = x := by simp
      rw [h0]
      exact hd
    simpa [Function.comp] using hd'.comp 0 h2
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (f (x + t * (-gx)) - f x)) (𝓝[≠] (0 : ℝ))
      (𝓝 (gx * (-gx))) := by
    have h := hasDerivAt_iff_tendsto_slope_zero.mp hpath
    simpa [smul_eq_mul] using h
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (fun t ht => ne_of_gt ht)
  have hslope' : Tendsto (fun t : ℝ => t⁻¹ * (f (x + t * (-gx)) - f x)) (𝓝[>] (0 : ℝ))
      (𝓝 (gx * (-gx))) := hslope.mono_left hle
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * (f (x + t * (-gx)) - f x) < 0 :=
    hslope'.eventually_lt tendsto_const_nhds hneg
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨-gx, ε / 2, by linarith, ?_⟩
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε ∩ Ioi (0 : ℝ) := by
    refine ⟨?_, by show (0 : ℝ) < ε / 2; linarith⟩
    rw [Metric.mem_ball, Real.dist_eq]
    rw [show ε / 2 - 0 = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have hq : (ε / 2)⁻¹ * (f (x + (ε / 2) * (-gx)) - f x) < 0 := hsub ht
  have hpos : 0 < ε / 2 := by linarith
  have hlt : f (x + (ε / 2) * (-gx)) - f x < 0 := by
    by_contra h
    push_neg at h
    have hdiv : (ε / 2)⁻¹ * (f (x + (ε / 2) * (-gx)) - f x)
        = (f (x + (ε / 2) * (-gx)) - f x) / (ε / 2) := by ring
    rw [hdiv] at hq
    have := div_nonneg h (le_of_lt hpos)
    linarith
  linarith

/-! ## 注：闭环语义
  · 二阶充分条件（极小 / 极大）+ 二阶必要条件（RealKKTSecondOrder）+ f''=0 的不可判定性
    = 一维二阶条件的完整图景；
  · `IsSaddle` 与 `saddle_second_deriv_zero` 说明：一维鞍点恰好是「二阶信息不足」的驻点；
  · `no_saddle_in_convex` 说明凸性使鞍点消失（驻点即全局最小）；
  · `descent_direction_exists` 给出梯度下降方向的局部下降依据，衔接 RealGradDescent；
  · 多维鞍点（Hessian 不定）在 RealHessian 中以二次型正定性刻画。 -/

end Lattice
