import Mathlib
import Lattice.Lib.Convex.RealKKT
import Lattice.Lib.Optim.RealStationarity
/-!
# LATTICE: KKT 二阶条件 —— 一维情形

RealKKT 给出增广拉格朗日的**一阶**驻点（∂/∂x = 0 ∧ ∂/∂λ = 0 ⟺ 约束满足 ∧ 乘子归零）；
RealStationarity 给出一致标量系统的驻点 ⟺ 满足点。本文件补上**二阶**判别：

  1. `IsStrictLocalMin`（def）：∃δ>0，∀y ≠ x，|y−x| < δ ⟹ f(x) < f(y)；
     `IsStrictLocalMin.toIsLocalMin`：严格局部极小 ⟹ 局部极小；
  2. `strict_local_min_of_deriv_sign`（**MVT 引擎**）：若 f 在 (x−η, x+η) 上连续可微，
     且导数在 x 左右**异号**（∀z ≠ x，(z−x)·f'(z) > 0），则 x 是严格局部极小。
     证明：对 [y,x] 或 [x,y] 用 Lagrange 中值定理（`exists_deriv_eq_slope`），
     由 f'(c) 的符号判定 f(y) − f(x)；
  3. `second_order_sufficient`（**二阶充分条件**）：f 在 (x−δ, x+δ) 上连续、可微、
     f' 连续、**f'' > 0** 且 f'(x) = 0 ⟹ x 是严格局部极小。
     证明：`strictMonoOn_of_deriv_pos` 应用于 f' 得 f' 严格递增，配合 f'(x) = 0
     给出导数异号，再调用 2；
  4. `exists_box_of_continuousAt_neg` / `second_order_necessary`（**二阶必要条件**）：
     f 在 (x−δ, x+δ) 上连续、可微、f' 连续、**f'' 在 x 处连续**，且 x 是局部极小
     ⟹ f''(x) ≥ 0。证明（反证）：设 f''(x) < 0，由 f'' 的连续性取充分小的 η 使
     f'' < 0 于 (x−η, x+η)；`strictAntiOn_of_deriv_neg` 应用于 f' 得 f' 在 x 右侧
     严格下降，结合 f'(x) = 0（`IsLocalMin.deriv_eq_zero`）得 f'(y) < 0；
     对 [x,y] 用中值定理得 f(y) < f(x)，与局部极小矛盾；
  5. `kkt_deriv_quadratic` / `quadratic_unconstrained_stationary`：二次目标
     f(x) = a/2·x² + b·x 的导数 a·x + b，以及 a ≠ 0 时驻点 ⟺ x = −b/a；
  6. `IsKKTQuad`（def）/ `quadratic_kkt`（**二次问题的 KKT 完整刻画**）：
     min f(x) s.t. c·x ≤ d（c ≠ 0）的 KKT 系统 ⟺ 两个互斥分支：
       非活跃（c·x < d，λ = 0，a·x + b = 0）或
       活跃（c·x = d，x = d/c，λ = −(ax+b)/c ≥ 0）；
     （第一分支 `a·x + b = 0` 即无约束驻点条件；a ≠ 0 时等价于 x = −b/a。）
  7. `quadratic_kkt_minimal`（**KKT 充分性，凸情形**）：a > 0 且 x 满足 KKT ⟹ x 是
     可行域上的全局极小点。证明用恒等式 f(y) − f(x) = (y−x)·(a/2·(y−x) − λc) 与
     互补松弛的两种情形（λ = 0 / λ > 0 ⟹ c·x = d）；
  8. `LICQOneDim`（def）/ `deriv_affine` / `licq_one_dim`：一维仿射约束 g(x) = c·x − d 的
     LICQ ⟺ 约束梯度 c ≠ 0 ⟺ 导函数处处非零；
     `licq_one_dim_multiplier_unique`（**LICQ ⟹ 乘子唯一**）：c ≠ 0 时
     f'(x) + λ·c = 0 的乘子 λ 唯一；
  9. `KKTOneDim`（def）/ `kkt_one_dim_complete`（**一维 KKT 完整刻画**）：
     非活跃（c·x < d，λ = 0，f'(x) = 0——**正好回收 RealStationarity 的 P0 驻点**）
     或活跃（c·x = d，λ = −f'(x)/c ≥ 0）；
     `kkt_one_dim_inactive_stationary`：非活跃分支 ⟹ f'(x) = 0（与 P0 的显式衔接）。

诚实边界：
  · 结论只覆盖**一维**（单决策变量、单个仿射约束）。多维/多约束的 LICQ（约束梯度线性无关）
    与二阶条件需要 Hessian 的（半）正定性；mathlib 4.14 有有限维内积空间与二次型工具，
    但本仓库未引入 Hessian 的形式化，故标注为后续工作。
  · 二阶必要/充分条件都以**区间上的连续可微性 + f'' 的正负性**表述，而非仅「f'' 在 x 处
    存在」的点条件：点形式的经典证明需要 Taylor–Peano 余项（f(y) = f(x) + f'(x)(y−x)
    + ½f''(x)(y−x)² + o((y−x)²)），mathlib 4.14 的 `taylor_mean_remainder*` 要求
    `ContDiffOn`（高阶可微）而非二阶点条件，故此处把「f、f'、f'' 在区间上的连续性」
    显式写为假设——这是经典教材的标准前提，**未被弱化**，只是被写成了显式形式。
    ⭐ **第八节部分补上了这一条**：`second_order_sufficient_pointwise` 把
    **「f'' > 0 于整个区间」降为「f''(x) > 0 于点」**（外加 f'' 在 x 的点连续性），
    结论不变 ⟹ 假设**严格更弱**。⚠ **但"Taylor–Peano"本身仍未做到**：
    见第八节 8.3 的诚实清单。
  · `quadratic_kkt` 的 KKT 刻画是**纯代数等价**（对 a 的符号无要求，只需 c ≠ 0）；
    `quadratic_kkt_minimal` 的**全局最优性**才需要凸性（a > 0）。二者分开陈述，
    以避免把「KKT 系统的代数结构」与「凸性给出的最优性」混为一谈。
  · 一维 KKT ⟺ 分支刻画依赖约束为**仿射**（单个约束的 LICQ 只需 c ≠ 0）。
    非线性约束 g 的 LICQ 需 g'(x) ≠ 0 在活跃点成立；本文件以 `LICQOneDim c := c ≠ 0`
    抽象该条件，并用 `deriv_affine` 说明它等价于仿射约束的梯度非零。
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Lattice

/-! ## 一、严格局部极小的定义与基本性质 -/

/-- **严格局部极小**：存在 δ > 0，使 x 的 δ-邻域内所有 y ≠ x 满足 f(x) < f(y)。 -/
def IsStrictLocalMin (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ y, y ≠ x → |y - x| < δ → f x < f y

/-- 严格局部极小 ⟹ 局部极小（把球邻域改写为 `IsLocalMin` 的滤子形式）。 -/
theorem IsStrictLocalMin.toIsLocalMin {f : ℝ → ℝ} {x : ℝ} (h : IsStrictLocalMin f x) :
    IsLocalMin f x := by
  obtain ⟨δ, hδ, hmin⟩ := h
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  by_cases hyx : y = x
  · subst hyx; exact le_rfl
  · refine le_of_lt (hmin y hyx ?_)
    rw [Metric.mem_ball, Real.dist_eq] at hy
    exact hy

/-! ## 二、中值定理引擎：导数异号 ⟹ 严格局部极小 -/

/-- **MVT 引擎**：f 在 (x−η, x+η) 上连续可微，且 ∀z ≠ x，(z−x)·f'(z) > 0
（导数在 x 左侧为负、右侧为正），则 x 是严格局部极小。

证明：对 y < x 用 Lagrange 中值定理（在 [y,x] 上）取得 c，
f'(c) = (f x − f y)/(x − y)；由 c < x 知 (c−x)·f'(c) > 0 而 c−x < 0，
故 f'(c) < 0，进而 f x − f y < 0；y > x 时对称。 -/
theorem strict_local_min_of_deriv_sign (f : ℝ → ℝ) (x η : ℝ) (hη : 0 < η)
    (hf_cont : ContinuousOn f (Ioo (x - η) (x + η)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - η) (x + η)))
    (hsign : ∀ z ∈ Ioo (x - η) (x + η), z ≠ x → 0 < (z - x) * deriv f z) :
    ∀ y, y ≠ x → |y - x| < η → f x < f y := by
  intro y hyx hy
  rw [abs_lt] at hy
  have hymem : y ∈ Ioo (x - η) (x + η) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsub_yx : Icc y x ⊆ Ioo (x - η) (x + η) := by
    intro t ht
    rw [mem_Icc] at ht
    exact ⟨by linarith [ht.1, hymem.1], by linarith [ht.2]⟩
  have hsub_xy : Icc x y ⊆ Ioo (x - η) (x + η) := by
    intro t ht
    rw [mem_Icc] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2, hymem.2]⟩
  rcases lt_trichotomy y x with hlt | heq | hgt
  · -- y < x
    obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope f hlt (hf_cont.mono hsub_yx)
      (hf_diff.mono fun t ht => hsub_yx (Ioo_subset_Icc_self ht))
    have hcmem : c ∈ Ioo (x - η) (x + η) := hsub_yx (Ioo_subset_Icc_self hc)
    have hcx : c ≠ x := by linarith [hc.2]
    have hprod := hsign c hcmem hcx
    have hdc : deriv f c < 0 := by
      have hneg : c - x < 0 := by linarith [hc.2]
      by_contra h
      push_neg at h
      have : (c - x) * deriv f c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) h
      linarith
    have hnum : f x - f y < 0 := by
      have hq : (f x - f y) / (x - y) < 0 := by rw [← hcval]; exact hdc
      by_contra hle
      push_neg at hle
      have : 0 ≤ (f x - f y) / (x - y) := div_nonneg hle (by linarith)
      linarith
    linarith
  · exact absurd heq hyx
  · -- x < y
    obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope f hgt (hf_cont.mono hsub_xy)
      (hf_diff.mono fun t ht => hsub_xy (Ioo_subset_Icc_self ht))
    have hcmem : c ∈ Ioo (x - η) (x + η) := hsub_xy (Ioo_subset_Icc_self hc)
    have hcx : c ≠ x := by linarith [hc.1]
    have hprod := hsign c hcmem hcx
    have hdc : 0 < deriv f c := by
      have hpos : 0 < c - x := by linarith [hc.1]
      by_contra h
      push_neg at h
      have : (c - x) * deriv f c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) h
      linarith
    have hnum : 0 < f y - f x := by
      have hq : 0 < (f y - f x) / (y - x) := by rw [← hcval]; exact hdc
      by_contra hle
      push_neg at hle
      have : (f y - f x) / (y - x) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hle (by linarith)
      linarith
    linarith

/-! ## 三、二阶充分条件 -/

/-- **二阶充分条件**：f 在 (x−δ, x+δ) 上连续、可微、f' 连续、f'' 处处为正，且 f'(x) = 0，
则 x 是**严格局部极小**。

证明：`strictMonoOn_of_deriv_pos` 应用于 f'（在开区间上 interior = 自身）得 f' 严格递增；
于是 z > x 时 f'(z) > f'(x) = 0、z < x 时 f'(z) < 0，即导数在 x 左右异号；
在 δ/2 邻域上调用 `strict_local_min_of_deriv_sign`。 -/
theorem second_order_sufficient (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hf_cont : ContinuousOn f (Ioo (x - δ) (x + δ)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - δ) (x + δ)))
    (hf'_cont : ContinuousOn (deriv f) (Ioo (x - δ) (x + δ)))
    (hf''_pos : ∀ z ∈ Ioo (x - δ) (x + δ), 0 < deriv (deriv f) z)
    (hstat : deriv f x = 0) : IsStrictLocalMin f x := by
  have hmono : StrictMonoOn (deriv f) (Ioo (x - δ) (x + δ)) :=
    strictMonoOn_of_deriv_pos (convex_Ioo (x - δ) (x + δ)) hf'_cont fun z hz => by
      rw [interior_Ioo] at hz
      exact hf''_pos z hz
  have hsubset : Ioo (x - δ / 2) (x + δ / 2) ⊆ Ioo (x - δ) (x + δ) := by
    intro t ht
    rw [mem_Ioo] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hxmem : x ∈ Ioo (x - δ) (x + δ) := ⟨by linarith, by linarith⟩
  have hsign : ∀ z ∈ Ioo (x - δ / 2) (x + δ / 2), z ≠ x → 0 < (z - x) * deriv f z := by
    intro z hz hzx
    have hzmem : z ∈ Ioo (x - δ) (x + δ) := hsubset hz
    rcases lt_trichotomy z x with hlt | heq | hgt
    · have hd : deriv f z < 0 := by
        have h := hmono hzmem hxmem hlt
        rwa [hstat] at h
      exact mul_pos_of_neg_of_neg (by linarith) hd
    · exact absurd heq hzx
    · have hd : 0 < deriv f z := by
        have h := hmono hxmem hzmem hgt
        rwa [hstat] at h
      exact mul_pos (by linarith) hd
  exact ⟨δ / 2, by linarith,
    strict_local_min_of_deriv_sign f x (δ / 2) (by linarith)
      (hf_cont.mono hsubset) (hf_diff.mono hsubset) hsign⟩

/-! ## 四、二阶必要条件 -/

/-- g 在 x 处连续且 g(x) < 0 ⟹ 存在充分小的盒子使 g 在盒内严格为负。 -/
theorem exists_box_of_continuousAt_neg (g : ℝ → ℝ) {x δ : ℝ} (hδ : 0 < δ)
    (hg : ContinuousAt g x) (hneg : g x < 0) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∀ z, |z - x| < η → g z < 0 := by
  have hev : ∀ᶠ z in 𝓝 x, g z < 0 := hg.tendsto.eventually (Iio_mem_nhds hneg)
  have hmem : {z : ℝ | g z < 0} ∈ 𝓝 x := hev
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min δ ε / 2, ?_, ?_, ?_⟩
  · have : 0 < min δ ε := lt_min hδ hε
    linarith
  · have : min δ ε ≤ δ := min_le_left _ _
    linarith
  · intro z hz
    refine hsub ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have : min δ ε ≤ ε := min_le_right _ _
    linarith

/-- **二阶必要条件**：f 在 (x−δ, x+δ) 上连续、可微、f' 连续、f'' 在 x 处连续，
且 x 是**局部极小** ⟹ f''(x) ≥ 0。

证明（反证）：设 f''(x) < 0。由 `exists_box_of_continuousAt_neg` 取 η ≤ δ 使 f'' < 0 于
(x−η, x+η)（取 η = min(η₁, r)/2，r 为局部极小邻域半径）；`strictAntiOn_of_deriv_neg`
应用于 f' 得 f' 严格递减，故 y > x 时 f'(y) < f'(x) = 0（`IsLocalMin.deriv_eq_zero`）；
对 [x,y] 用中值定理得 f(y) − f(x) = f'(c)(y−x) < 0，即 f(y) < f(x)，
与 y 落在局部极小邻域内矛盾。 -/
theorem second_order_necessary (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hmin : IsLocalMin f x)
    (hf_cont : ContinuousOn f (Ioo (x - δ) (x + δ)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - δ) (x + δ)))
    (hf'_cont : ContinuousOn (deriv f) (Ioo (x - δ) (x + δ)))
    (hf''_cont : ContinuousAt (deriv (deriv f)) x) :
    0 ≤ deriv (deriv f) x := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨η₁, hη₁, hη₁_δ, hη₁p⟩ :=
    exists_box_of_continuousAt_neg (deriv (deriv f)) hδ hf''_cont hcon
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hmin
  set m : ℝ := min η₁ r / 2 with hm
  have hmpos : 0 < m := by
    have : 0 < min η₁ r := lt_min hη₁ hr
    simp only [hm]; linarith
  have hmη₁ : m ≤ η₁ := by
    have : min η₁ r ≤ η₁ := min_le_left _ _
    simp only [hm]; linarith
  have hmr : m < r := by
    have : min η₁ r ≤ r := min_le_right _ _
    simp only [hm]; linarith
  have hmδ : m ≤ δ := le_trans hmη₁ hη₁_δ
  have hsub : Ioo (x - m) (x + m) ⊆ Ioo (x - δ) (x + δ) := by
    intro t ht
    rw [mem_Ioo] at ht ⊢
    constructor <;> linarith [ht.1, ht.2, hmδ]
  have hanti : StrictAntiOn (deriv f) (Ioo (x - m) (x + m)) :=
    strictAntiOn_of_deriv_neg (convex_Ioo (x - m) (x + m)) (hf'_cont.mono hsub) fun z hz => by
      rw [interior_Ioo] at hz
      exact hη₁p z (by
        rw [abs_lt]
        constructor <;> linarith [hz.1, hz.2, hmη₁])
  have hxmem : x ∈ Ioo (x - m) (x + m) := ⟨by linarith, by linarith⟩
  have hymem : x + m / 2 ∈ Ioo (x - m) (x + m) := ⟨by linarith, by linarith⟩
  have hxy : x < x + m / 2 := by linarith
  have hdylt : deriv f (x + m / 2) < deriv f x := hanti hxmem hymem hxy
  have hstat : deriv f x = 0 := hmin.deriv_eq_zero
  rw [hstat] at hdylt
  have hy_in : |(x + m / 2) - x| < r := by
    rw [show x + m / 2 - x = m / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have hminy : f x ≤ f (x + m / 2) :=
    hrsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hy_in)
  have hsub_xy : Icc x (x + m / 2) ⊆ Ioo (x - δ) (x + δ) := by
    intro t ht
    rw [mem_Icc] at ht
    exact hsub ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  obtain ⟨c, hc, hcval⟩ := exists_deriv_eq_slope f hxy (hf_cont.mono hsub_xy)
    (hf_diff.mono fun t ht => hsub_xy (Ioo_subset_Icc_self ht))
  have hcmem : c ∈ Ioo (x - m) (x + m) := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hdc : deriv f c < 0 := by
    have h := hanti hxmem hcmem hc.1
    rwa [hstat] at h
  have hneg : f (x + m / 2) - f x < 0 := by
    have hq : (f (x + m / 2) - f x) / (x + m / 2 - x) < 0 := by rw [← hcval]; exact hdc
    by_contra hle
    push_neg at hle
    have hpos : 0 < x + m / 2 - x := by linarith
    have : 0 ≤ (f (x + m / 2) - f x) / (x + m / 2 - x) := div_nonneg hle (le_of_lt hpos)
    linarith
  linarith

/-! ## 五、二次问题：导数、驻点与 KKT 完整刻画 -/

/-- 二次目标 f(x) = a/2·x² + b·x 的导数：a·x + b。 -/
theorem kkt_deriv_quadratic (a b x : ℝ) :
    deriv (fun y : ℝ => a / 2 * y ^ 2 + b * y) x = a * x + b := by
  have h1 : HasDerivAt (fun y : ℝ => a / 2 * y ^ 2) (a / 2 * (2 * x)) x := by
    simpa using ((hasDerivAt_id x).pow 2).const_mul (a / 2)
  have h2 : HasDerivAt (fun y : ℝ => b * y) b x := by
    simpa using (hasDerivAt_id x).const_mul b
  have h := h1.add h2
  rw [h.deriv]
  ring

/-- 二次目标的**无约束驻点**：a ≠ 0 时 f'(x) = 0 ⟺ x = −b/a。 -/
theorem quadratic_unconstrained_stationary (a b x : ℝ) (ha : a ≠ 0) :
    deriv (fun y : ℝ => a / 2 * y ^ 2 + b * y) x = 0 ↔ x = -b / a := by
  rw [kkt_deriv_quadratic]
  constructor
  · intro h
    have hx : a * x = -b := by linarith
    calc x = a * x / a := by rw [mul_div_cancel_left₀ x ha]
      _ = -b / a := by rw [hx]
  · intro h
    rw [h]
    have h1 : a * (-b / a) = -b := by
      rw [mul_comm, div_mul_cancel₀ (-b) ha]
    rw [h1]
    ring

/-- **二次问题的 KKT 系统**（min a/2·x² + b·x s.t. c·x ≤ d）：
可行性 c·x ≤ d、驻点 a·x + b + λ·c = 0、对偶可行 λ ≥ 0、互补松弛 λ(c·x − d) = 0。 -/
def IsKKTQuad (a b c d x lam : ℝ) : Prop :=
  c * x ≤ d ∧ a * x + b + lam * c = 0 ∧ 0 ≤ lam ∧ lam * (c * x - d) = 0

/-- **二次问题的 KKT 完整刻画**：c ≠ 0 时 KKT 系统 ⟺ 两个互斥分支——
**非活跃**（c·x < d，a·x + b = 0，λ = 0：约束不起作用，KKT 退化为无约束驻点）
或**活跃**（c·x = d，x = d/c，λ = −(a·x+b)/c ≥ 0）。

（纯代数等价，对 a 的符号无要求；全局最优性见 `quadratic_kkt_minimal`。a ≠ 0 时
第一分支的 `a·x + b = 0` 等价于 `x = −b/a`。） -/
theorem quadratic_kkt (a b c d x lam : ℝ) (hc : c ≠ 0) :
    IsKKTQuad a b c d x lam ↔
      (c * x < d ∧ a * x + b = 0 ∧ lam = 0) ∨
      (c * x = d ∧ x = d / c ∧ lam = -(a * x + b) / c ∧ 0 ≤ lam) := by
  constructor
  · rintro ⟨hfeas, hstat, hlam, hcs⟩
    rcases lt_or_eq_of_le hfeas with hlt | heq
    · have hlam0 : lam = 0 := by
        rcases mul_eq_zero.mp hcs with h | h
        · exact h
        · exact absurd h (by linarith)
      refine Or.inl ⟨hlt, ?_, hlam0⟩
      rw [hlam0] at hstat
      linarith
    · have hlc : lam * c = -(a * x + b) := by linarith
      have hlam' : lam = -(a * x + b) / c := (eq_div_iff_mul_eq hc).mpr hlc
      have hx : x = d / c := (eq_div_iff_mul_eq hc).mpr (by rw [mul_comm]; exact heq)
      exact Or.inr ⟨heq, hx, hlam', hlam⟩
  · rintro (⟨hlt, hstat0, hlam0⟩ | ⟨heq, hx, hlam, hlam0⟩)
    · refine ⟨le_of_lt hlt, ?_, le_of_eq hlam0.symm, by rw [hlam0]; ring⟩
      rw [hlam0, hstat0]
      ring
    · subst hx
      have hlc : lam * c = -(a * (d / c) + b) := (eq_div_iff_mul_eq hc).mp hlam
      refine ⟨le_of_eq heq, ?_, hlam0, by rw [heq]; ring⟩
      rw [hlc]
      ring

/-- **二次问题的 KKT 充分性（凸情形）**：a > 0 且 x 满足 KKT ⟹ x 是可行域
{y | c·y ≤ d} 上的**全局极小点**。

证明：由驻点 a·x + b = −λc 得恒等式
    f(y) − f(x) = (y − x)·(a/2·(y − x) − λc) = a/2·(y−x)² − λ·(c·(y−x))。
若 λ = 0，第一项非负；若 λ > 0，互补松弛给出 c·x = d，故 c·y ≤ d = c·x
即 c·(y−x) ≤ 0，第二项亦非负。 -/
theorem quadratic_kkt_minimal (a b c d x lam : ℝ) (ha : 0 < a)
    (hkkt : IsKKTQuad a b c d x lam) :
    ∀ y : ℝ, c * y ≤ d → a / 2 * x ^ 2 + b * x ≤ a / 2 * y ^ 2 + b * y := by
  obtain ⟨hfeas, hstat, hlam, hcs⟩ := hkkt
  intro y hy
  have hstat' : a * x + b = -lam * c := by linarith
  have hfact : a / 2 * y ^ 2 + b * y - (a / 2 * x ^ 2 + b * x)
      = (y - x) * (a / 2 * (y - x) - lam * c) := by
    have h1 : a / 2 * (y + x) + b = a / 2 * (y - x) - lam * c := by
      have h2 : a / 2 * (y + x) + b = a / 2 * (y - x) + (a * x + b) := by ring
      rw [h2, hstat']; ring
    have h3 : a / 2 * y ^ 2 + b * y - (a / 2 * x ^ 2 + b * x)
        = (y - x) * (a / 2 * (y + x) + b) := by ring
    rw [h3, h1]
  have hnonneg : 0 ≤ (y - x) * (a / 2 * (y - x) - lam * c) := by
    rcases eq_or_lt_of_le hlam with h0 | hpos
    · rw [← h0]
      have h2 : (y - x) * (a / 2 * (y - x) - 0 * c) = a / 2 * (y - x) ^ 2 := by ring
      rw [h2]
      exact mul_nonneg (by linarith) (sq_nonneg _)
    · have hcxd : c * x - d = 0 := (mul_eq_zero.mp hcs).resolve_left (ne_of_gt hpos)
      have hle : c * (y - x) ≤ 0 := by
        have : c * y ≤ c * x := by linarith [hy, hcxd]
        linarith
      have h1 : lam * (c * (y - x)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) hle
      have h2 : (y - x) * (a / 2 * (y - x) - lam * c)
          = a / 2 * (y - x) ^ 2 - lam * (c * (y - x)) := by ring
      rw [h2]
      have h3 : 0 ≤ a / 2 * (y - x) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      linarith
  rw [← hfact] at hnonneg
  linarith

/-! ## 六、一维 LICQ 与一维 KKT 完整刻画 -/

/-- **一维 LICQ**（单仿射约束 c·x − d ≤ 0）：约束梯度 c 非零。 -/
def LICQOneDim (c : ℝ) : Prop := c ≠ 0

/-- 仿射函数 g(x) = c·x − d 的导数等于 c。 -/
theorem deriv_affine (c d x : ℝ) : deriv (fun y : ℝ => c * y - d) x = c := by
  have h : HasDerivAt (fun y : ℝ => c * y - d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).sub (hasDerivAt_const x d)
  exact h.deriv

/-- **一维 LICQ 判据**：LICQ ⟺ 约束函数的导函数处处非零（⟺ c ≠ 0）。 -/
theorem licq_one_dim (c d : ℝ) :
    LICQOneDim c ↔ ∀ x : ℝ, deriv (fun y : ℝ => c * y - d) x ≠ 0 := by
  constructor
  · intro hc x
    rw [deriv_affine]
    exact hc
  · intro h
    have h0 := h 0
    rwa [deriv_affine] at h0

/-- **LICQ ⟹ 乘子唯一**：一维仿射约束下驻点方程 f'(x) + λ·c = 0 的乘子唯一。 -/
theorem licq_one_dim_multiplier_unique (f : ℝ → ℝ) (c x : ℝ) (hc : c ≠ 0)
    (lam₁ lam₂ : ℝ) (h₁ : deriv f x + lam₁ * c = 0) (h₂ : deriv f x + lam₂ * c = 0) :
    lam₁ = lam₂ := by
  have h : (lam₁ - lam₂) * c = 0 := by linarith
  have hz : lam₁ - lam₂ = 0 := (mul_eq_zero.mp h).resolve_right hc
  linarith

/-- **一维 KKT 系统**（min f s.t. c·x ≤ d）：
可行性、驻点、对偶可行、互补松弛。 -/
def KKTOneDim (f : ℝ → ℝ) (c d x lam : ℝ) : Prop :=
  c * x ≤ d ∧ deriv f x + lam * c = 0 ∧ 0 ≤ lam ∧ lam * (c * x - d) = 0

/-- **一维 KKT 完整刻画**：c ≠ 0 时 KKT ⟺ 两个互斥分支——
非活跃（c·x < d，λ = 0，**f'(x) = 0**，即 RealStationarity 的 P0 驻点条件）
或活跃（c·x = d，λ = −f'(x)/c ≥ 0）。 -/
theorem kkt_one_dim_complete (f : ℝ → ℝ) (c d x lam : ℝ) (hc : c ≠ 0) :
    KKTOneDim f c d x lam ↔
      (c * x < d ∧ lam = 0 ∧ deriv f x = 0) ∨
      (c * x = d ∧ lam = -(deriv f x) / c ∧ 0 ≤ lam) := by
  constructor
  · rintro ⟨hfeas, hstat, hlam, hcs⟩
    rcases lt_or_eq_of_le hfeas with hlt | heq
    · have hlam0 : lam = 0 := by
        rcases mul_eq_zero.mp hcs with h | h
        · exact h
        · exact absurd h (by linarith)
      refine Or.inl ⟨hlt, hlam0, ?_⟩
      rw [hlam0] at hstat
      simpa using hstat
    · have hlc : lam * c = -(deriv f x) := by linarith
      exact Or.inr ⟨heq, (eq_div_iff_mul_eq hc).mpr hlc, hlam⟩
  · rintro (⟨hlt, hlam0, hstat⟩ | ⟨heq, hlam, hlam0⟩)
    · refine ⟨le_of_lt hlt, ?_, le_of_eq hlam0.symm, by rw [hlam0]; ring⟩
      rw [hlam0, hstat]
      ring
    · have hlc : lam * c = -(deriv f x) := (eq_div_iff_mul_eq hc).mp hlam
      refine ⟨le_of_eq heq, ?_, hlam0, by rw [heq]; ring⟩
      rw [hlc]
      ring

/-- **衔接 RealStationarity**：一维 KKT 的非活跃分支给出 f'(x) = 0——
正是 P0 的标量驻点条件（约束不活跃时 KKT 退化为无约束驻点）。 -/
theorem kkt_one_dim_inactive_stationary (f : ℝ → ℝ) (c d x lam : ℝ) (hc : c ≠ 0)
    (hkkt : KKTOneDim f c d x lam) (hinactive : c * x < d) :
    deriv f x = 0 := by
  rcases (kkt_one_dim_complete f c d x lam hc).mp hkkt with h | ⟨heq, -⟩
  · exact h.2.2
  · exact absurd heq (ne_of_lt hinactive)

/-! ## 七、把区间光滑性假设升级为定理（WP6 / ROADMAP B1）

上文 `second_order_sufficient` / `second_order_necessary` 把「`f` 在区间上连续、可微、
`f'` 连续、`f''` 连续」写成**显式假设**（docstring 第 50–54 行说明这是「经典教材的
标准前提，未被弱化，只是被写成了显式形式」）。

本节把这个「显式假设包」**收敛成一条 `ContDiffOn ℝ 2 f` 假设**，
并证明**其余全部是定理**（不再需要外部逐条提供）：

    `contDiff_two_gives_interval_hypotheses`：
        `ContDiffOn ℝ 2 f (Ioo (x−δ) (x+δ))`  ⟹
        `ContinuousOn f I ∧ DifferentiableOn ℝ f I ∧ ContinuousOn (deriv f) I
         ∧ ∀ z ∈ I, HasDerivAt (deriv f) (deriv (deriv f) z) z`

即 `hf_cont` / `hf_diff` / `hf'_cont` 与「`f'` 在区间上可导且导数为 `f''`」**同时**成为
定理；`ContDiffOn ℝ 2` 是**一条**假设而不是四条，且是本仓库最小的高阶光滑性原语。

由此回收出**单假设版**二阶充分/必要条件：

    · `second_order_sufficient_of_contDiff`：
        只需 `ContDiffOn ℝ 2 f I` + `f'' > 0` 于 `I` + `f'(x) = 0` ⟹ x 严格局部极小；
    · `second_order_necessary_of_contDiff`：
        只需 `ContDiffOn ℝ 2 f I` + x 局部极小 ⟹ `f''(x) ≥ 0`；
        原版的点条件 `ContinuousAt (deriv (deriv f)) x` 也由 `ContDiffOn ℝ 2` 免费产出。

**诚实边界（本节）**：这里的升级是**假设的合并与自动化**，不是命题的削弱——两个
`_of_contDiff` 版与原版**结论完全相同**，只是把「三条区间假设 + 一条点假设」换成
「一条 `ContDiffOn ℝ 2`」。真正的点条件（仅假设 `f''` 在 x 点存在）仍需要
Taylor–Peano 余项，mathlib 4.14 的 `taylor_mean_remainder*` 要求 `ContDiffOn`，
故**未做**（与原 docstring 一致，未改变结论强度）。 -/

/-- **`ContDiffOn ℝ 2` 展开为区间光滑性假设包**（把 `RealKKTSecondOrder` 的显式假设
`hf_cont`/`hf_diff`/`hf'_cont` 以及「`f'` 的导数是 `f''`」一次性全部变成定理）。

证明：
  · `hf_cont`：`ContDiffOn.continuousOn`；
  · `hf_diff`：`ContDiffOn.differentiableOn`（`1 ≤ 2`）；
  · `hf'_cont`：`ContDiffOn.continuousOn_iteratedDerivWithin`（`1 ≤ 2`，`UniqueDiffOn`）后
    用 `iteratedDerivWithin_one` 与开区间 `UniqueDiffWithinAt` 化为 `deriv f`；
  · `hf''`：`ContDiffOn.differentiableOn_iteratedDerivWithin`（`1 < 2`）给出
    `deriv f` 在区间上可导，再用 `DifferentiableOn.differentiableAt`（开区间是邻域）取 `HasDerivAt`。 -/
theorem contDiff_two_gives_interval_hypotheses (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 2 f (Ioo (x - δ) (x + δ))) :
    ContinuousOn f (Ioo (x - δ) (x + δ)) ∧
    DifferentiableOn ℝ f (Ioo (x - δ) (x + δ)) ∧
    ContinuousOn (deriv f) (Ioo (x - δ) (x + δ)) ∧
    (∀ z ∈ Ioo (x - δ) (x + δ),
      HasDerivAt (deriv f) (deriv (deriv f) z) z) := by
  set I : Set ℝ := Ioo (x - δ) (x + δ) with hI
  have hIopen : IsOpen I := isOpen_Ioo
  have huniq : UniqueDiffOn ℝ I := hI ▸ uniqueDiffOn_Ioo (x - δ) (x + δ)
  have hxmem : x ∈ I := ⟨by linarith, by linarith⟩
  have hnhds : I ∈ 𝓝 x := hIopen.mem_nhds hxmem
  -- 局部：在 I 上 `deriv f` 与 `iteratedDerivWithin 1 f I` 一致（用 `derivWithin` 中转）
  have hdw : ∀ z ∈ I, derivWithin f I z = deriv f z := fun z hz =>
    derivWithin_of_mem_nhds (hIopen.mem_nhds hz)
  have h1eq : ∀ z ∈ I, deriv f z = iteratedDerivWithin 1 f I z := fun z hz => by
    rw [iteratedDerivWithin_one (huniq z hz), hdw z hz]
  refine ⟨hf.continuousOn, hf.differentiableOn (by norm_num), ?_, ?_⟩
  · -- `deriv f` 在 I 上连续
    have h1 : ContinuousOn (iteratedDerivWithin 1 f I) I :=
      hf.continuousOn_iteratedDerivWithin (by norm_num) huniq
    exact h1.congr h1eq
  · -- `deriv f` 在 I 上可导，导数为 `deriv (deriv f)`
    intro z hz
    have h2 : DifferentiableOn ℝ (iteratedDerivWithin 1 f I) I :=
      hf.differentiableOn_iteratedDerivWithin (by norm_num) huniq
    have hzI : I ∈ 𝓝 z := hIopen.mem_nhds hz
    have hd : DifferentiableAt ℝ (iteratedDerivWithin 1 f I) z := h2.differentiableAt hzI
    have hev : deriv f =ᶠ[𝓝 z] iteratedDerivWithin 1 f I := by
      filter_upwards [hzI] with w hw
      exact h1eq w hw
    have hd' : DifferentiableAt ℝ (deriv f) z := hd.congr_of_eventuallyEq hev
    refine (hd'.hasDerivAt).congr_of_eventuallyEq ?_
    filter_upwards [hzI] with w hw
    show deriv f w = deriv f w
    rfl

/-- **二阶充分条件（单假设版 / WP6 升级）**：把 `second_order_sufficient` 的四条区间假设
（`hf_cont`、`hf_diff`、`hf'_cont`、以及 `f''` 的可微性）**合并为一条
`ContDiffOn ℝ 2 f (Ioo (x−δ) (x+δ))`**，其余保留 `f'' > 0` 于区间与驻点条件。

结论与 `second_order_sufficient` **完全一致**（不弱化）：`x` 是严格局部极小。

证明：`contDiff_two_gives_interval_hypotheses` 一次性产出原版所需的全部区间假设，
再调用 `second_order_sufficient`。 -/
theorem second_order_sufficient_of_contDiff (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 2 f (Ioo (x - δ) (x + δ)))
    (hf''_pos : ∀ z ∈ Ioo (x - δ) (x + δ), 0 < deriv (deriv f) z)
    (hstat : deriv f x = 0) : IsStrictLocalMin f x := by
  obtain ⟨hc, hd, hdc, _⟩ := contDiff_two_gives_interval_hypotheses f x δ hδ hf
  exact second_order_sufficient f x δ hδ hc hd hdc hf''_pos hstat

/-- **二阶必要条件（单假设版 / WP6 升级）**：把 `second_order_necessary` 的**四条**区间假设
（`hf_cont`、`hf_diff`、`hf'_cont`）以及**点条件** `ContinuousAt (deriv (deriv f)) x`
**全部**合并为一条 `ContDiffOn ℝ 2 f (Ioo (x−δ) (x+δ))`。

结论与 `second_order_necessary` **完全一致**（不弱化）：`0 ≤ f''(x)`。

证明要点：`ContDiffOn ℝ 2` 给出 `iteratedDerivWithin 2 f I` 在 `I` 上连续
（`ContDiffOn.continuousOn_iteratedDerivWithin`，取 `m = 2 ≤ 2`）；而在开区间 `I` 上
`iteratedDerivWithin 2 f I = deriv (deriv f)`（`iteratedDerivWithin_succ` +
`iteratedDerivWithin_one` + `derivWithin_of_mem_nhds`），故 `deriv (deriv f)` 在 `x`
连续——**原本那条点假设 `hf''_cont` 由 `ContDiffOn` 免费产出**。

**升级性质**：这是**纯粹的假设合并**，不引入任何更强的新假设，也不弱化结论。 -/
theorem second_order_necessary_of_contDiff (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hmin : IsLocalMin f x)
    (hf : ContDiffOn ℝ 2 f (Ioo (x - δ) (x + δ))) :
    0 ≤ deriv (deriv f) x := by
  obtain ⟨hc, hd, hdc, _⟩ := contDiff_two_gives_interval_hypotheses f x δ hδ hf
  -- `f''` 在 x 处连续：由 `ContDiffOn` 给出 `iteratedDerivWithin 2 f I` 在 I 上连续，
  -- 它在 x 的邻域内等于 `deriv (deriv f)`，故 `deriv (deriv f)` 在 x 连续
  set I : Set ℝ := Ioo (x - δ) (x + δ) with hI
  have hIopen : IsOpen I := isOpen_Ioo
  have huniq : UniqueDiffOn ℝ I := hI ▸ uniqueDiffOn_Ioo (x - δ) (x + δ)
  have hxmem : x ∈ I := ⟨by linarith, by linarith⟩
  have hcont2 : ContinuousOn (iteratedDerivWithin 2 f I) I :=
    hf.continuousOn_iteratedDerivWithin (by norm_num) huniq
  -- 在 I 上 `iteratedDerivWithin 2 f I = deriv (deriv f)`
  have heq : ∀ z ∈ I, iteratedDerivWithin 2 f I z = deriv (deriv f) z := fun z hz => by
    have hzI : I ∈ 𝓝 z := hIopen.mem_nhds hz
    -- `iteratedDerivWithin 2 = derivWithin (iteratedDerivWithin 1)`；再把两处 within 去掉
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ (huniq z hz)]
    have hfun : iteratedDerivWithin 1 f I =ᶠ[𝓝 z] deriv f := by
      filter_upwards [hzI] with w hw
      rw [iteratedDerivWithin_one (huniq w hw), derivWithin_of_mem_nhds (hIopen.mem_nhds hw)]
    rw [derivWithin_of_mem_nhds hzI, hfun.deriv_eq]
  have hev : iteratedDerivWithin 2 f I =ᶠ[𝓝 x] deriv (deriv f) := by
    filter_upwards [hIopen.mem_nhds hxmem] with z hz
    exact heq z hz
  have hcontat : ContinuousAt (deriv (deriv f)) x :=
    (hcont2.continuousAt (hIopen.mem_nhds hxmem)).congr hev
  exact second_order_necessary f x δ hδ hmin hc hd hdc hcontat

/-! ## 注：与既有一阶结果的关系
  · RealKKT 的 `P4_augmented_stationarity`：增广拉格朗日的一阶驻点 ⟺ 约束满足 ∧ λ = 0；
    本文件补充**二阶**判别（f''(x*) ≥ 0 必要、f''(x*) > 0 充分），
    构成「一阶：驻点定位；二阶：认证极小」的完整链条。
  · RealStationarity 的 `P0_scalar_stationarity`：本文件的 `kkt_one_dim_inactive_stationary`
    与 `quadratic_unconstrained_stationary` 在**约束不活跃**时回收该结论。
  · 二次问题的 `quadratic_kkt_minimal` 是「凸 + KKT ⟹ 全局最优」在一维仿射约束下的
    完整可证实例，与 RealDualTheory 的弱对偶/互补松弛互为佐证（后者是乘子视角，
    前者是直接比较视角）。
  · 第七节（WP6）：`contDiff_two_gives_interval_hypotheses` 把区间光滑性假设包升级为定理，
    `second_order_sufficient_of_contDiff` / `second_order_necessary_of_contDiff` 给出单假设版。 -/

/-! ## 八、⭐ **点式二阶充分条件**：把「`f'' > 0` 于整个区间」降为「`f'' x > 0` 于点」

### 8.1 立项（为什么这不是第七节的重述）

第七节的 `second_order_sufficient_of_contDiff` 虽把**光滑性**假设合并为一条
`ContDiffOn ℝ 2 f I`，但它**仍要求** `∀ z ∈ I, 0 < deriv (deriv f) z`
——即 `f'' > 0` 必须**在整个区间**上成立。这是**区间**条件。

⭐ 本节把这一条降为**点条件** `0 < deriv (deriv f) x`（**只在 `x` 一点**），
代价仅是 `f''` 在 `x` 处**连续**（同样是点条件）：

    `second_order_sufficient_pointwise`：
        `ContinuousAt (deriv (deriv f)) x` + `0 < deriv (deriv f) x` + `deriv f x = 0`
        + `f`/`f'` 在区间上连续可微
        ⟹ `IsStrictLocalMin f x`。

⚠ **假设对比（严格更弱，可逐条核对）**：
  · 第七节：`ContDiffOn ℝ 2 f I` **且** `∀z ∈ I, 0 < f'' z`（**区间**上的正性）；
  · 本节：`ContinuousOn f I`、`DifferentiableOn f I`、`ContinuousOn f' I`
    （区间上的 C¹，**弱于** `ContDiffOn ℝ 2`）**且** `ContinuousAt f'' x`、
    `0 < f'' x`（**点**条件）。
  ⇒ ⭐ **结论相同**（都是 `IsStrictLocalMin f x`），**假设严格更弱** ⟹ 不是重述。

### 8.2 证明机制（**复用本文件已有的引擎**）

关键观察：本文件的 `exists_box_of_continuousAt_neg`（第四节）已经能把
**点式连续性**转成**盒子**。那里用于**必要**条件（`f''(x) < 0` ⟹ 取盒使 `f'' < 0`）；
⭐ 本节把它**反向**用于**充分**条件（`f''(x) > 0` ⟹ 取盒使 `f'' > 0`），
再把盒内的一致正性喂给**已有的** `second_order_sufficient`（第三节）。

⇒ ⭐ 这是**真接线**：没有新增数学，但把一条**区间假设**换成了**点假设**。 -/

/-- `g` 在 `x` 处连续且 `0 < g x` ⟹ 存在充分小的盒子使 `g` 在盒内严格为正。

⭐ 证明：把本文件第四节的 `exists_box_of_continuousAt_neg` 应用于 `−g`
（`g x > 0` ⟺ `(−g) x < 0`），再把结论的符号翻回来。**复用已有引擎，无新数学。**

⚠⚠ **命名订正（2026-09-24）**：本定理原名为 `exists_box_of_continuousAt_pos`，
**与 `RealSaddlePoint.lean:162` 的同名定理冲突**（**同一 `Lattice` 扁平命名空间**）——
⚠ **且 `RealSaddlePoint.lean:2` 自己 import 本文件 ⟹ 该 root 模块无法被 import**
（**内核实证**：`environment already contains 'Lattice.exists_box_of_continuousAt_pos'
from RealKKTSecondOrder`）。
⭐ **引入时间**：`RealSaddlePoint` 侧的该定理出自 `985a57b`（wave 8）；
**本侧是 B249 `2e10f29` 才追加的** ⟹ **故由本侧改名**（加 `_kkt` 后缀）。
⚠ **两侧陈述**同型但**不是同一个引理**（本侧走 `−g` 引擎），**故改名而非删除**。 -/
theorem exists_box_of_continuousAt_pos_kkt (g : ℝ → ℝ) {x δ : ℝ} (hδ : 0 < δ)
    (hg : ContinuousAt g x) (hpos : g x > 0) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∀ z, |z - x| < η → 0 < g z := by
  have hgn : ContinuousAt (fun z => -g z) x :=
    (continuous_neg.continuousAt).comp hg
  have hneg : (fun z => -g z) x < 0 := by simpa using hpos
  obtain ⟨η, hη, hηδ, hbox⟩ := exists_box_of_continuousAt_neg (fun z => -g z) hδ hgn hneg
  exact ⟨η, hη, hηδ, fun z hz => by have := hbox z hz; linarith⟩

/-- ⭐ **点式二阶充分条件**：`f`/`f'` 在 `(x−δ, x+δ)` 上连续可微，
`f''` **在 `x` 处连续**且 `f''(x) > 0`（**点条件**），`f'(x) = 0`
⟹ `x` 是 `f` 的**严格局部极小点**。

**与第七节的对比**：结论相同，但把第七节的**区间**假设 `∀z ∈ I, 0 < f'' z`
降为**点**假设 `0 < f'' x`（外加 `f''` 在 `x` 的点连续性）⟹ **严格更弱**。

证明：`exists_box_of_continuousAt_pos_kkt` 把点正性转成盒内一致正性（半径取 `min δ η`），
再调用第三节的 `second_order_sufficient`。 -/
theorem second_order_sufficient_pointwise (f : ℝ → ℝ) (x δ : ℝ) (hδ : 0 < δ)
    (hf_cont : ContinuousOn f (Ioo (x - δ) (x + δ)))
    (hf_diff : DifferentiableOn ℝ f (Ioo (x - δ) (x + δ)))
    (hf'_cont : ContinuousOn (deriv f) (Ioo (x - δ) (x + δ)))
    (hf''_cont : ContinuousAt (deriv (deriv f)) x)
    (hf''_pos : 0 < deriv (deriv f) x)
    (hstat : deriv f x = 0) : IsStrictLocalMin f x := by
  obtain ⟨η, hηpos, hηδ, hbox⟩ :=
    exists_box_of_continuousAt_pos_kkt (deriv (deriv f)) hδ hf''_cont hf''_pos
  -- 用 `η` 作为新的盒子半径：`η ≤ δ` ⟹ 盒子嵌套
  have hsubset : Ioo (x - η) (x + η) ⊆ Ioo (x - δ) (x + δ) := by
    intro t ht
    rw [mem_Ioo] at ht ⊢
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact second_order_sufficient f x η hηpos (hf_cont.mono hsubset) (hf_diff.mono hsubset)
    (hf'_cont.mono hsubset) (fun z hz => hbox z (by
      rw [abs_lt]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩)) hstat

/-! **注（必要条件无需升级）**：第四节的 `second_order_necessary` 其陈述**已经**是点式的
（假设即为 `ContinuousAt (deriv (deriv f)) x`），故本节**不**重复声明「点式必要条件」，
以免制造近同名声明（STYLE 的重名治理）。本节的升级**只针对充分条件**。

### 8.3 ⚠ 诚实清单：**做到了什么** / **没做到什么**

**做到了**（本节的产出，均为定理）：
  · **已否证 / 历史沿革（原 `exists_box_of_continuousAt_pos`）**：该定理在本文件中现名为
    `exists_box_of_continuousAt_pos_kkt`（上方 docstring 记录了 2026-09-24 的改名，
    原因是与 `RealSaddlePoint.lean` 侧同名定理在同一 `Lattice` 扁平命名空间冲突）；
    `g` 在 `x` 连续、`g x > 0` ⟹ 盒子内 `g > 0`
    （**复用**第四节 `exists_box_of_continuousAt_neg`，把 `g` 换成 `−g`）；
  · `second_order_sufficient_pointwise`：要点 **点式充分条件**（`f''(x) > 0` **于点**）。

**注意 明确没做到（这不是"Taylor–Peano"）**：
  · 本节的点式条件仍要求 **`f''` 在 `x` 处连续**（`ContinuousAt (deriv (deriv f)) x`）
    与 **`f`/`f'` 在区间上连续可微**。**古典的 Taylor–Peano 定理**只要求
    「`f''(x)` **存在**」（不要求连续），并给出 `f(y) = f(x) + f'(x)(y−x)
    + ½f''(x)(y−x)² + o((y−x)²)`。**本节没有证明该定理，也没有用它**；
  · 原因（**已 grep 核实，非猜测**）：`Mathlib/Analysis/Calculus/Taylor.lean`
    的 `## TODO` 逐字登记 `* the Peano form of the remainder` ⟹
    要点 **mathlib 确实没有 Peano 余项**（B214 因①：名字真的不存在）。
    故「仅 `f''(x)` 存在 ⟹ 二阶充分」在 mathlib 4.14 下**需要新理论**，不是接线；
  · 另一条可能的路线 —— `HasStrictFDerivAt`（严格导数，`FDeriv/Basic.lean:154`，
    带 `hasStrictFDerivAt_iff_isLittleO`）**能给** `o(·)` 展开，
    但它是**二元**形式（`f x − f y − f'(x−y) = o(x−y)`），
    转成一元 Taylor 需要额外的 `Asymptotics` 机器；**本轮未做**，登记为后续工作。
    注意 该路线若做，假设仍是「`f'` 严格可导」（**强于**「`f''(x)` 存在」），
    故它**仍不等于**古典 Peano 定理对假设的最弱要求。 -/

end Lattice
