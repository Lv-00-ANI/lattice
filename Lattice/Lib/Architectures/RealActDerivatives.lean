import Mathlib
import Lattice.Lib.Architectures.RealActComplete
import Lattice.Lib.Architectures.RealActClass
/-!
# LATTICE: 激活导数界（反向传播基础）

在 `RealActComplete` / `RealActClass` 的激活族（`sigmoid` / `hardSigmoid` / `silu` /
`geluTanh` / `tanh`）之上补齐**导数公式与界**，作为反向传播与 Lipschitz 常数的依据：

  1. `softplus`：`softplus x = log (1 + exp x)`；`softplus_hasDerivAt`（导数 = sigmoid）、
     `softplus_deriv`、`softplus_pos`、`softplus_strictMono`（用 exp/log 单调，避免导数）、
     `softplus_lipschitz`（1-Lipschitz，经 MVT + `sigmoid_bounds`）；
  2. `sigmoid_deriv_pos`、`sigmoid_deriv_le_quarter`（`deriv σ ≤ 1/4`，回收 `sigmoid_deriv`
     与 `sigmoid_bounds`）；
  3. `tanh_deriv_nonneg`、`tanh_deriv_le_one`（回收 `tanh_deriv` 与 `tanh_abs_le_one`）；
  4. `hardSigmoid_eq_linear_of_mem`（`|x| < 3` 时 `hardSigmoid x = x/6 + 1/2`）与
     `hardSigmoid_hasDerivAt_linear`（该区域内导数为 `1/6`，用 `HasDerivAt.congr_of_eventuallyEq`）；
  5. GELU-tanh 的导数：`geluInner`（内层 `sqrt(2/π)·(x + 0.044715 x³)`）、
     `geluInner_hasDerivAt`、`geluSoftMask_hasDerivAt`、`geluTanh_hasDerivAt`（乘积法则
     + 链式法则），以及闭式 `geluTanhDeriv` 与 `geluTanh_deriv`。

诚实标注（无 sorry / axiom / admit）：
- **精确（erf 版）GELU 不在范围内**：mathlib 4.14 无 `erf`，本文件只做 **tanh 近似版**
  `geluTanh`（其定义在 `RealActClass`）。`geluTanhDeriv` 是链式法则给出的闭式，
  **未**证明其全局有界/Lipschitz 常数（GELU-tanh 的导数界超出本文件范围）。
- `softplus_lipschitz` 的常数是 **1**（非 sharp 的 1/4；sharp 版需要 `sigmoid ≤ 1/4`
  的精确取到论证，本文件不追求）。
- `hardSigmoid` 在 `x = ±3` 处不可导；本文件只证**开区间** `(-3, 3)` 内的导数，
  全局导数公式**未证**。
- 复用（只读）`RealActComplete` / `RealActClass` 的既有引理，不重复证明。
-/

noncomputable section

open scoped Topology

open Lattice.Lib.Architectures.RealActClass

namespace Lattice
/-! ## 一、softplus 与它的导数 -/

/-- softplus：`log (1 + exp x)`（ReLU 的光滑近似）。 -/
def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

/-- **softplus 的导数 = sigmoid**。 -/
theorem softplus_hasDerivAt (x : ℝ) : HasDerivAt softplus (sigmoid x) x := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + Real.exp t) (Real.exp x) x :=
    (Real.hasDerivAt_exp x).const_add 1
  have hden : (1 + Real.exp x) ≠ 0 := by positivity
  have hlog : HasDerivAt (Real.log ∘ fun t : ℝ => 1 + Real.exp t)
      ((1 + Real.exp x)⁻¹ * Real.exp x) x :=
    (Real.hasDerivAt_log hden).comp x h1
  have hval : (1 + Real.exp x)⁻¹ * Real.exp x = sigmoid x := by
    unfold sigmoid
    rw [Real.exp_neg]
    have h1' : (1 + Real.exp x) ≠ 0 := by positivity
    have h2' : (1 + (Real.exp x)⁻¹) ≠ 0 := by positivity
    field_simp
    ring
  rw [hval] at hlog
  simpa [softplus, Function.comp_def] using hlog

theorem softplus_deriv (x : ℝ) : deriv softplus x = sigmoid x := (softplus_hasDerivAt x).deriv

theorem softplus_pos (x : ℝ) : 0 < softplus x := by
  unfold softplus
  exact Real.log_pos (by linarith [Real.exp_pos x])

/-- softplus 严格单调（用 exp/log 单调，不经导数）。 -/
theorem softplus_strictMono : StrictMono softplus := by
  intro x y hxy
  unfold softplus
  exact Real.log_lt_log (by positivity) (by linarith [Real.exp_lt_exp.mpr hxy])

/-- softplus 是 1-Lipschitz（导数 = sigmoid ∈ (0,1)，MVT）。 -/
theorem softplus_lipschitz (x y : ℝ) : |softplus x - softplus y| ≤ 1 * |x - y| := by
  have hf : ∀ z : ℝ, z ∈ Set.univ → DifferentiableAt ℝ softplus z :=
    fun z _ => (softplus_hasDerivAt z).differentiableAt
  have hbound : ∀ z : ℝ, z ∈ Set.univ → ‖deriv softplus z‖ ≤ 1 := by
    intro z _
    rw [softplus_deriv, Real.norm_eq_abs, abs_of_pos (sigmoid_bounds z).1]
    exact le_of_lt (sigmoid_bounds z).2
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (x := x) (y := y) (s := Set.univ)
    hf hbound convex_univ trivial trivial
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt

/-! ## 二、sigmoid 导数界 -/

theorem sigmoid_deriv_pos (x : ℝ) : 0 < deriv sigmoid x := by
  rw [sigmoid_deriv]
  exact mul_pos (sigmoid_bounds x).1 (by linarith [(sigmoid_bounds x).2])

/-- `deriv σ ≤ 1/4`（标准最大斜率）。 -/
theorem sigmoid_deriv_le_quarter (x : ℝ) : deriv sigmoid x ≤ 1 / 4 := by
  rw [sigmoid_deriv]
  nlinarith [sq_nonneg (sigmoid x - 1 / 2), (sigmoid_bounds x).1, (sigmoid_bounds x).2]

/-! ## 三、tanh 导数界 -/

theorem tanh_deriv_nonneg (x : ℝ) : 0 ≤ deriv Real.tanh x := by
  rw [tanh_deriv]
  have h : Real.tanh x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (tanh_abs_le_one x)
  linarith

theorem tanh_deriv_le_one (x : ℝ) : deriv Real.tanh x ≤ 1 := by
  rw [tanh_deriv]
  nlinarith [sq_nonneg (Real.tanh x)]

/-! ## 四、hardSigmoid 的线性段与导数 -/

/-- `|x| < 3` 时 hardSigmoid 退化为线性函数 `x/6 + 1/2`。 -/
theorem hardSigmoid_eq_linear_of_mem {x : ℝ} (h1 : -3 < x) (h2 : x < 3) :
    hardSigmoid x = x / 6 + 1 / 2 := by
  unfold hardSigmoid
  have hpos : 0 ≤ x / 6 + 1 / 2 := by linarith
  have hle : x / 6 + 1 / 2 ≤ 1 := by linarith
  rw [max_eq_right hpos, min_eq_right hle]

/-- **hardSigmoid 在线性段 `(-3,3)` 内可导且导数为 `1/6`**。 -/
theorem hardSigmoid_hasDerivAt_linear {x : ℝ} (h1 : -3 < x) (h2 : x < 3) :
    HasDerivAt hardSigmoid (1 / 6) x := by
  have hlin : HasDerivAt (fun t : ℝ => t / 6 + 1 / 2) (1 / 6) x := by
    have h := ((hasDerivAt_id x).div_const 6).const_add (1 / 2)
    simpa [add_comm] using h
  have hev : hardSigmoid =ᶠ[𝓝 x] fun t : ℝ => t / 6 + 1 / 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with t ht
    exact hardSigmoid_eq_linear_of_mem ht.1 ht.2
  exact hlin.congr_of_eventuallyEq hev

/-! ## 五、GELU-tanh 的导数（链式法则） -/

/-- GELU-tanh 的内层：`sqrt(2/π) · (x + 0.044715 x³)`。 -/
def geluInner (x : ℝ) : ℝ := Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3)

theorem geluInner_hasDerivAt (x : ℝ) :
    HasDerivAt geluInner (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2)) x := by
  have hinner : HasDerivAt (fun t : ℝ => t + 0.044715 * t ^ 3)
      (1 + 0.044715 * (3 * x ^ 2)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun t : ℝ => 0.044715 * t ^ 3) (0.044715 * (3 * x ^ 2)) x := by
      have hp : HasDerivAt (fun t : ℝ => t ^ 3) ((3 : ℝ) * x ^ (3 - 1)) x := hasDerivAt_pow 3 x
      simpa using hp.const_mul 0.044715
    exact h1.add h2
  have hres := hinner.const_mul (Real.sqrt (2 / Real.pi))
  have hval : Real.sqrt (2 / Real.pi) * (1 + 0.044715 * (3 * x ^ 2))
      = Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2) := by ring
  rw [hval] at hres
  show HasDerivAt (fun y : ℝ => Real.sqrt (2 / Real.pi) * (y + 0.044715 * y ^ 3))
    (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2)) x
  exact hres

/-- GELU-tanh 软掩码 `0.5 * (1 + tanh (geluInner x))` 的导数。 -/
theorem geluSoftMask_hasDerivAt (x : ℝ) :
    HasDerivAt geluSoftMask
      (0.5 * ((1 - Real.tanh (geluInner x) ^ 2)
        * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2)))) x := by
  have htanh : HasDerivAt (fun t : ℝ => Real.tanh (geluInner t))
      ((1 - Real.tanh (geluInner x) ^ 2)
        * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))) x :=
    (tanh_hasDerivAt (geluInner x)).comp x (geluInner_hasDerivAt x)
  have h := (htanh.const_add 1).const_mul 0.5
  simpa [geluSoftMask] using h

/-- **GELU-tanh 的导数（乘积法则 + 链式法则）**：`geluTanh x = x · geluSoftMask x`。 -/
theorem geluTanh_hasDerivAt (x : ℝ) :
    HasDerivAt geluTanh
      (geluSoftMask x + x * (0.5 * ((1 - Real.tanh (geluInner x) ^ 2)
        * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))))) x := by
  have h := (hasDerivAt_id x).mul (geluSoftMask_hasDerivAt x)
  simpa [geluTanh] using h

/-- GELU-tanh 导数的闭式（链式法则的结果）。 -/
noncomputable def geluTanhDeriv (x : ℝ) : ℝ :=
  geluSoftMask x + x * (0.5 * ((1 - Real.tanh (geluInner x) ^ 2)
    * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))))

theorem geluTanh_deriv (x : ℝ) : deriv geluTanh x = geluTanhDeriv x :=
  (geluTanh_hasDerivAt x).deriv

end Lattice
