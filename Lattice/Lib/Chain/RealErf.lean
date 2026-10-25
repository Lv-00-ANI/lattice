import Mathlib

/-!
# LATTICE: 自证误差函数 `erf` —— 定义、奇性、单调、导数与有界性

mathlib 4.14 **没有** `Real.erf`（已确认全库无 `erf`），而 GELU 的精确版本
`gelu(x) = x·Φ(x)`、`Φ(x) = (1 + erf(x/√2))/2` 需要它。本文件用 Lebesgue
区间积分**自证**一个误差函数：

    erf x = (2 / √π) · ∫₀ˣ e^{−t²} dt

并给出下列性质（全部真证，无 sorry/axiom/admit）：

  1. `erf_zero`：`erf 0 = 0`（积分区间退化）；
  2. `erf_neg`：**奇函数** `erf(−x) = −erf x`
     （区间积分换元 `intervalIntegral.integral_comp_neg` + 被积函数偶性 `neg_sq`）；
  3. `erf_hasDerivAt` / `erf_deriv`：**导数闭式** `erf' x = (2/√π)·e^{−x²}`
     （用微积分基本定理 `Continuous.integral_hasStrictDerivAt`，被积函数连续）；
  4. `erf_strictMono` / `erf_monotone`：**严格单调递增**（导数恒正，`strictMono_of_deriv_pos`）；
  5. `erf_pos_of_pos`：正半轴取正值；
  6. `erf_abs_le_one`：**有界** `|erf x| ≤ 1`——关键是半线高斯积分
     `integral_gaussian_Ioi 1 : ∫_{Ioi 0} e^{−t²} = √π/2`
     （mathlib 已证），配合 `setIntegral_mono_set`（非负被积函数在 `Ioc 0 X ⊆ Ioi 0`
     上单调）得到 `∫₀ˣ e^{−t²} ≤ √π/2`，再乘 `2/√π` 得 `erf x ≤ 1`；
     负半轴用奇性约化；
  7. `erf_bounded` / `erf_bddAbove`：`erf` 的值域有界（即 `lim_{x→∞}` 的有界性；
     **不求极限值**，只给全局界 `|erf| ≤ 1`）。

诚实标注（中文关键词）：
  · 常数 `2/√π` 的归一化使 `|erf| ≤ 1` **恰好**成立（这依赖高斯积分值 `√π`，
    此处只读复用 mathlib 的 `integral_gaussian_Ioi`；本文件**未**自证该积分）；
  · `erf` 是**唯一**满足 `erf 0 = 0` 且导数 `= (2/√π)e^{−x²}` 的函数——
    该唯一性在 docstring 中**标注**（此处未形式化，见 §注）；
  · 未证 `erf` 的级数展开、未证 `lim_{x→∞} erf x = 1`（只证有界，按要求）。
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped Topology

open MeasureTheory

namespace Lattice

/-- 自证误差函数：`erf x = (2/√π) · ∫₀ˣ e^{−t²} dt`
（mathlib 4.14 无 `Real.erf`，用区间积分定义）。 -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

/-- 高斯被积函数 `t ↦ e^{−t²}` 连续（求导与积分的基石）。 -/
theorem continuous_exp_neg_sq :
    Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) :=
  Real.continuous_exp.comp ((continuous_id.pow 2).neg)

/-! ## 一、基本值 -/

/-- `erf 0 = 0`（积分区间退化为一点）。 -/
@[simp] theorem erf_zero : erf 0 = 0 := by
  unfold erf
  simp

/-! ## 二、奇性 -/

/-- **`erf` 是奇函数**：`erf (−x) = −erf x`。
证明：用 `integral_comp_neg`（`a = 0`、`b = −x`）把 `∫₀^{−x} f(−t)` 换成
`∫_{x}^{0} f`，被积函数偶（`neg_sq`），再用 `integral_symm` 换向。 -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  unfold erf
  have hmain : (∫ t in (0 : ℝ)..(-x), Real.exp (-(t ^ 2)))
      = -∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2)) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -x)
      (f := fun t : ℝ => Real.exp (-(t ^ 2)))
    have heven : (fun t : ℝ => Real.exp (-((-t) ^ 2)))
        = (fun t : ℝ => Real.exp (-(t ^ 2))) := by
      funext t
      rw [neg_sq]
    rw [heven] at h
    simp only [neg_neg, neg_zero] at h
    rw [intervalIntegral.integral_symm (a := (0 : ℝ)) (b := x)] at h
    exact h
  rw [hmain]
  ring

/-! ## 三、导数（微积分基本定理） -/

/-- **`erf` 的导数**：`erf' x = (2/√π)·e^{−x²}`
（`Continuous.integral_hasStrictDerivAt` + 常数倍）。 -/
theorem erf_hasDerivAt (x : ℝ) :
    HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(x ^ 2))) x := by
  have h := (continuous_exp_neg_sq.integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt
  have h2 := h.const_mul (2 / Real.sqrt Real.pi)
  unfold erf
  exact h2

/-- 导数的 `deriv` 形式。 -/
theorem erf_deriv (x : ℝ) : deriv erf x = (2 / Real.sqrt Real.pi) * Real.exp (-(x ^ 2)) :=
  (erf_hasDerivAt x).deriv

/-! ## 四、单调性 -/

/-- `erf` 严格单调递增（导数恒正）。 -/
theorem erf_strictMono : StrictMono erf := by
  refine strictMono_of_deriv_pos (fun x => ?_)
  rw [erf_deriv]
  positivity

/-- `erf` 单调递增。 -/
theorem erf_monotone : Monotone erf := erf_strictMono.monotone

/-- 正自变量处 `erf` 取正值。 -/
theorem erf_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < erf x := by
  have h := erf_strictMono hx
  rwa [erf_zero] at h

/-! ## 五、有界性 `|erf x| ≤ 1` -/

/-- 高斯被积函数在 `Ioi 0` 上可积（`integrable_exp_neg_mul_sq` 的 `b = 1` 特例）。 -/
theorem integrableOn_exp_neg_sq_Ioi :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Set.Ioi (0 : ℝ)) volume := by
  have h : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) volume := by
    simpa using (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num))
  exact h.integrableOn

/-- 半线高斯积分：`∫_{Ioi 0} e^{−t²} = √π/2`
（只读复用 mathlib 的 `integral_gaussian_Ioi`）。 -/
theorem integral_exp_neg_sq_Ioi :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) = Real.sqrt Real.pi / 2 := by
  have h := integral_gaussian_Ioi (1 : ℝ)
  simpa using h

/-- 非负被积函数在半线上的单调性：`0 ≤ X ⟹ ∫₀ˣ e^{−t²} ≤ √π/2`
（`Ioc 0 X ⊆ Ioi 0` + `setIntegral_mono_set`）。 -/
theorem integral_exp_neg_sq_zero_to_le (X : ℝ) (hX : 0 ≤ X) :
    (∫ t in (0 : ℝ)..X, Real.exp (-(t ^ 2))) ≤ Real.sqrt Real.pi / 2 := by
  have hsub : Set.Ioc (0 : ℝ) X ⊆ Set.Ioi (0 : ℝ) := fun t ht => ht.1
  have hstep : (∫ t in Set.Ioc (0 : ℝ) X, Real.exp (-(t ^ 2)))
      ≤ (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) :=
    setIntegral_mono_set (f := fun t : ℝ => Real.exp (-(t ^ 2)))
      (s := Set.Ioc (0 : ℝ) X) (t := Set.Ioi (0 : ℝ)) (μ := volume)
      integrableOn_exp_neg_sq_Ioi
      (Filter.Eventually.of_forall (fun t => (Real.exp_pos (-(t ^ 2))).le)) hsub.eventuallyLE
  calc (∫ t in (0 : ℝ)..X, Real.exp (-(t ^ 2)))
      = (∫ t in Set.Ioc (0 : ℝ) X, Real.exp (-(t ^ 2))) :=
        intervalIntegral.integral_of_le hX
    _ ≤ (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t ^ 2))) := hstep
    _ = Real.sqrt Real.pi / 2 := integral_exp_neg_sq_Ioi

/-- 归一化常数满足 `(2/√π)·(√π/2) = 1`。 -/
theorem two_div_sqrt_pi_mul_sqrt_pi_div_two :
    (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
  rw [div_mul_div_comm, mul_comm (Real.sqrt Real.pi) 2]
  exact div_self (by positivity)

/-- **`erf` 有界**：`|erf x| ≤ 1`（负半轴由奇性约化到正半轴）。 -/
theorem erf_abs_le_one (x : ℝ) : |erf x| ≤ 1 := by
  have hbound : ∀ X : ℝ, 0 ≤ X → erf X ≤ 1 := by
    intro X hX
    unfold erf
    have hI := integral_exp_neg_sq_zero_to_le X hX
    have hc : 0 < 2 / Real.sqrt Real.pi := by positivity
    calc (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..X, Real.exp (-(t ^ 2))
        ≤ (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hI (le_of_lt hc)
      _ = 1 := two_div_sqrt_pi_mul_sqrt_pi_div_two
  rcases le_or_lt 0 x with hx | hx
  · rw [abs_of_nonneg]
    · exact hbound x hx
    · simpa using erf_monotone hx
  · have hx' : 0 ≤ -x := le_of_lt (neg_pos.mpr hx)
    have h1 : erf (-x) ≤ 1 := hbound (-x) hx'
    rw [erf_neg] at h1
    have hupper : erf x ≤ 1 := by
      have hle : erf x ≤ erf 0 := erf_monotone (le_of_lt hx)
      have h0 : erf x ≤ 0 := by simpa [erf_zero] using hle
      linarith
    rw [abs_le]
    exact ⟨by linarith, hupper⟩

/-- **值域有界**（`lim_{x→∞}` 的有界性；不求极限值）：`∃ M, ∀ x, |erf x| ≤ M`。 -/
theorem erf_bounded : ∃ M : ℝ, ∀ x : ℝ, |erf x| ≤ M :=
  ⟨1, erf_abs_le_one⟩

/-- `erf` 的值域有上界（单调 + 有界 ⟹ 收敛，此处只给有界性，按要求不求极限值）。 -/
theorem erf_bddAbove : BddAbove (Set.range erf) :=
  ⟨1, by rintro y ⟨x, rfl⟩; exact (abs_le.mp (erf_abs_le_one x)).2⟩

/-! ## 注：诚实边界
  · `erf` 的定义依赖 `∫₀ˣ e^{−t²}`（Lebesgue 区间积分）；导数用
    `Continuous.integral_hasStrictDerivAt`（FTC），**未**用任何公理。
  · 有界性 `|erf| ≤ 1` 的常数 `1` 依赖高斯积分 `∫_{Ioi 0} e^{−t²} = √π/2`；
    该积分由 mathlib 的 `integral_gaussian_Ioi` 提供（**只读复用**，本文件未重证）。
  · **唯一性（标注，未形式化）**：若 `g : ℝ → ℝ` 满足 `g 0 = 0` 且在每点
    `HasDerivAt g ((2/√π)e^{−x²})`，则 `g = erf`——因为 `g − erf` 的导数恒为 `0`，
    由 MVT 其为常函数，再由 `g 0 − erf 0 = 0` 定出常数 `0`。此唯一性此处只作
    文字讨论（**标注未证**），不影响 GELU 线对 `erf` 的使用。
  · **未证**：`erf` 的幂级数展开、`lim_{x→∞} erf x = 1`（仅证有界）。
-/

end Lattice
