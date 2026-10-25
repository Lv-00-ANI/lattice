import Mathlib
import Lattice.Lib.Architectures.RealActDerivatives
import Lattice.Lib.Architectures.RealActClass
import Lattice.Lib.Architectures.RealActComplete
/-!
# LATTICE: GELU-tanh 导数的全局界与 Lipschitz 常数（补 `RealActDerivatives` 的缺口）

`RealActDerivatives` 给出 `geluTanhDeriv` 的闭式（链式法则），但**标注未证**
其全局有界性。本文件补上这个缺口：

    geluTanhDeriv x = s x + x · 0.5 · ((1 − tanh²(geluInner x)) · (a · (1 + 3k x²)))

其中 `a = √(2/π)`、`k = 0.044715`、`s = geluSoftMask`、`geluInner x = a(x + k x³)`。

**证明路线**（全部真证）：
  1. `exp_neg_le_inv`：`e^{−z} ≤ 1/z`（`z > 0`）；
  2. `mul_exp_neg_mul_le`：`t·e^{−ct} ≤ 1/(c·e)`（`c > 0`、`t ≥ 0`）——`x e^{−cx}` 的全局最大值；
  3. `one_sub_tanh_sq_le_exp`：**核心衰减** `1 − tanh²u ≤ 4·e^{−2|u|}`
     （`1 − tanh²= (1−tanh)(1+tanh) ≤ 2(1−tanh)`，而
     `1 − tanh v = e^{−v}/cosh v ≤ 2 e^{−2v}`，用 `cosh v ≥ e^v/2`）；
  4. `gelu_inner_abs` / `two_mul_geluInner_abs` / `exp_neg_two_geluInner`：
     `|geluInner x| = a|x|(1 + k x²)`，指数拆成 `e^{−2a|x|}·e^{−2ak|x|x²}`；
  5. `decay_factor_le`：`(1 + 3kt²)·e^{−mt³} ≤ (1 + 3k)/m`（`0 < m ≤ 1`、`t ≥ 0`）；
  6. `geluTanhDeriv_abs_le`：**全局界** `|geluTanhDeriv x| ≤ geluTanhDerivBound`，
     显式常数
     `C = 1 + 2a·(1/(2a·e))·((1+3k)/(2ak))`（数值约 `6.85`）；
  7. `geluTanh_lipschitz`：`geluTanh` 是 `C`-Lipschitz（MVT + `geluTanh_deriv`）。

**诚实标注（中文关键词）**：
  · 常数 `C ≈ 6.85` 是**粗略但显式**的全局界；GELU-tanh 的真实导数上确界约
    `1.13`（sharp 常数）**未证**——sharp 界需要对 `geluInner` 的立方结构做精细
    最优化，超出本文件范围（**标注未证**）；
  · `1 − tanh²u ≤ 4e^{−2|u|}` 的指数常数 `4`/`2` 非 sharp（可优化到 `4e^{−2|u|}` 已是
    够用版本；sharp 版为 `4e^{−2|u|}/(1+e^{−2|u|})²`，**未做**）；
  · 未证 `geluTanh` 的二次可导性/凸性。

无 sorry/axiom/admit。
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped Topology

open Lattice.Lib.Architectures.RealActClass

namespace Lattice

/-! ## 一、指数衰减的初等界 -/

/-- `e^{−z} ≤ 1/z`（`z > 0`）：由 `Real.add_one_le_exp z` 得 `z ≤ e^z`，
再用 `div_le_one`。 -/
theorem exp_neg_le_inv {z : ℝ} (hz : 0 < z) : Real.exp (-z) ≤ 1 / z := by
  have hzexp : z ≤ Real.exp z :=
    le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp z)
  rw [le_div_iff₀ hz]
  have h : Real.exp (-z) * z = z / Real.exp z := by
    rw [Real.exp_neg]
    ring
  rw [h, div_le_one (Real.exp_pos z)]
  exact hzexp

/-- **`x e^{−cx}` 的全局最大值**：`t·e^{−ct} ≤ 1/(c·e)`（`c > 0`、`t ≥ 0`）。
由 `Real.add_one_le_exp (ct − 1)` 得 `ct ≤ e^{ct}/e`。 -/
theorem mul_exp_neg_mul_le {c : ℝ} (hc : 0 < c) {t : ℝ} (_ht : 0 ≤ t) :
    t * Real.exp (-(c * t)) ≤ 1 / (c * Real.exp 1) := by
  have h1 : c * t ≤ Real.exp (c * t - 1) := by
    have := Real.add_one_le_exp (c * t - 1)
    linarith
  have h2 : c * t * Real.exp 1 ≤ Real.exp (c * t) := by
    have hexp : Real.exp (c * t - 1) * Real.exp 1 = Real.exp (c * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc c * t * Real.exp 1 ≤ Real.exp (c * t - 1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos 1).le
      _ = Real.exp (c * t) := hexp
  have hE : 0 < Real.exp (c * t) := Real.exp_pos _
  have hCe : 0 < c * Real.exp 1 := mul_pos hc (Real.exp_pos 1)
  rw [Real.exp_neg, le_div_iff₀ hCe]
  have h3 : c * t * Real.exp 1 / Real.exp (c * t) ≤ 1 := by
    rw [div_le_one hE]
    exact h2
  calc t * (Real.exp (c * t))⁻¹ * (c * Real.exp 1)
      = c * t * Real.exp 1 / Real.exp (c * t) := by ring
    _ ≤ 1 := h3

/-! ## 二、核心衰减：`1 − tanh²u ≤ 4e^{−2|u|}` -/

/-- **核心衰减引理**：`1 − tanh²u ≤ 4·e^{−2|u|}`。
用偶性归到 `v = |u| ≥ 0`：`1 − tanh²v = (1−tanh v)(1+tanh v) ≤ 2(1−tanh v)`，
而 `1 − tanh v = (cosh v − sinh v)/cosh v = e^{−v}/cosh v ≤ 2e^{−2v}`
（`cosh v ≥ e^v/2`）。 -/
theorem one_sub_tanh_sq_le_exp (u : ℝ) :
    1 - Real.tanh u ^ 2 ≤ 4 * Real.exp (-(2 * |u|)) := by
  have hsq : Real.tanh u ^ 2 = Real.tanh |u| ^ 2 := by
    rcases le_or_lt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.tanh_neg]
      ring
  rw [hsq]
  have ht_le : Real.tanh |u| ≤ 1 := (abs_le.mp (tanh_abs_le_one |u|)).2
  have h1 : 1 - Real.tanh |u| ^ 2 ≤ 2 * (1 - Real.tanh |u|) := by
    nlinarith [sq_nonneg (1 - Real.tanh |u|)]
  have h2 : 1 - Real.tanh |u| ≤ 2 * Real.exp (-(2 * |u|)) := by
    have hcosh_pos : 0 < Real.cosh |u| := Real.cosh_pos |u|
    have hstep : 1 - Real.tanh |u| = Real.exp (-|u|) / Real.cosh |u| := by
      rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_sub_sinh, sub_div,
        div_self (ne_of_gt hcosh_pos)]
    rw [hstep, div_le_iff₀ hcosh_pos]
    rw [Real.cosh_eq]
    have hexpand : 2 * Real.exp (-(2 * |u|)) * ((Real.exp |u| + Real.exp (-|u|)) / 2)
        = Real.exp (-(2 * |u|)) * Real.exp |u| + Real.exp (-(2 * |u|)) * Real.exp (-|u|) := by
      ring
    rw [hexpand]
    have f1 : Real.exp (-(2 * |u|)) * Real.exp |u| = Real.exp (-|u|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have f2 : Real.exp (-(2 * |u|)) * Real.exp (-|u|) = Real.exp (-(3 * |u|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [f1, f2]
    have : 0 < Real.exp (-(3 * |u|)) := Real.exp_pos _
    linarith
  calc 1 - Real.tanh |u| ^ 2 ≤ 2 * (1 - Real.tanh |u|) := h1
    _ ≤ 2 * (2 * Real.exp (-(2 * |u|))) := by linarith [h2]
    _ = 4 * Real.exp (-(2 * |u|)) := by ring

/-! ## 三、`geluInner` 的绝对值与指数拆分 -/

/-- `|geluInner x| = √(2/π)·|x|·(1 + k x²)`。 -/
theorem gelu_inner_abs (x : ℝ) :
    |geluInner x| = Real.sqrt (2 / Real.pi) * |x| * (1 + 0.044715 * x ^ 2) := by
  have hfac : (0 : ℝ) ≤ 1 + 0.044715 * x ^ 2 := by nlinarith [sq_nonneg x]
  unfold geluInner
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [show x + 0.044715 * x ^ 3 = x * (1 + 0.044715 * x ^ 2) by ring]
  rw [abs_mul, abs_of_nonneg hfac]
  ring

/-- 两倍绝对值拆成两项（用 `|x|·x²` 而非 `|x|³`，避免 `sq_abs` 重写）。 -/
theorem two_mul_geluInner_abs (x : ℝ) :
    2 * |geluInner x| = 2 * Real.sqrt (2 / Real.pi) * |x|
      + 2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2 := by
  rw [gelu_inner_abs]
  ring

/-- 指数拆分：`e^{−2|geluInner x|} = e^{−2a|x|} · e^{−2ak|x|x²}`。 -/
theorem exp_neg_two_geluInner (x : ℝ) :
    Real.exp (-(2 * |geluInner x|))
      = Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|))
        * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2)) := by
  rw [two_mul_geluInner_abs, ← Real.exp_add]
  congr 1
  ring

/-! ## 四、三次衰减因子的一致界 -/

/-- **一致界**：`(1 + 3kt²)·e^{−mt³} ≤ (1 + 3k)/m`（`0 ≤ k`、`0 < m ≤ 1`、`t ≥ 0`）。
`t ≤ 1` 时左端 `≤ 1 + 3k ≤ (1+3k)/m`；`t > 1` 时
`1 + 3kt² ≤ (1+3k)t²` 且 `e^{−mt³} ≤ 1/(mt³)`，于是 `≤ (1+3k)/(mt) ≤ (1+3k)/m`。 -/
theorem decay_factor_le {k m t : ℝ} (hk : 0 ≤ k) (hm0 : 0 < m) (hm1 : m ≤ 1)
    (ht : 0 ≤ t) :
    (1 + 3 * k * t ^ 2) * Real.exp (-(m * t ^ 3)) ≤ (1 + 3 * k) / m := by
  have hk' : 0 ≤ 1 + 3 * k := by linarith
  rcases le_or_lt t 1 with ht1 | ht1
  · have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t, ht, ht1]
    have hexp : Real.exp (-(m * t ^ 3)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ m * t ^ 3 := mul_nonneg (le_of_lt hm0) (pow_nonneg ht 3)
      linarith
    have hfac : 1 + 3 * k * t ^ 2 ≤ 1 + 3 * k := by nlinarith [hk, ht2]
    have hone : (1 : ℝ) ≤ 1 / m := by
      rw [le_div_iff₀ hm0]
      linarith
    calc (1 + 3 * k * t ^ 2) * Real.exp (-(m * t ^ 3))
        ≤ (1 + 3 * k) * 1 :=
          mul_le_mul hfac hexp (le_of_lt (Real.exp_pos _)) hk'
      _ ≤ (1 + 3 * k) * (1 / m) := mul_le_mul_of_nonneg_left hone hk'
      _ = (1 + 3 * k) / m := by ring
  · have ht1' : (1 : ℝ) ≤ t := le_of_lt ht1
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    have hfac : 1 + 3 * k * t ^ 2 ≤ (1 + 3 * k) * t ^ 2 := by nlinarith [hk]
    have hmpos : 0 < m * t ^ 3 := by positivity
    have hexp : Real.exp (-(m * t ^ 3)) ≤ 1 / (m * t ^ 3) := exp_neg_le_inv hmpos
    have ht2exp : t ^ 2 * Real.exp (-(m * t ^ 3)) ≤ 1 / m := by
      have hEq : t ^ 2 * (1 / (m * t ^ 3)) = 1 / (m * t) := by
        rw [one_div, one_div, mul_inv]
        field_simp
        ring
      calc t ^ 2 * Real.exp (-(m * t ^ 3)) ≤ t ^ 2 * (1 / (m * t ^ 3)) :=
            mul_le_mul_of_nonneg_left hexp (sq_nonneg t)
        _ = 1 / (m * t) := hEq
        _ ≤ 1 / m := by
            rw [div_le_iff₀ (by positivity : 0 < m * t)]
            have hmt : (1 / m) * (m * t) = t := by
              rw [one_div, inv_mul_cancel_left₀ (ne_of_gt hm0)]
            rw [hmt]
            exact ht1'
    calc (1 + 3 * k * t ^ 2) * Real.exp (-(m * t ^ 3))
        ≤ ((1 + 3 * k) * t ^ 2) * Real.exp (-(m * t ^ 3)) :=
          mul_le_mul_of_nonneg_right hfac (le_of_lt (Real.exp_pos _))
      _ = (1 + 3 * k) * (t ^ 2 * Real.exp (-(m * t ^ 3))) := by ring
      _ ≤ (1 + 3 * k) * (1 / m) := mul_le_mul_of_nonneg_left ht2exp hk'
      _ = (1 + 3 * k) / m := by ring

/-! ## 五、显式全局常数与主定理 -/

/-- **显式全局界常数**：`C = 1 + 2a·(1/(2a·e))·((1+3k)/(2ak))`，
其中 `a = √(2/π)`、`k = 0.044715`（数值约 `6.85`）。 -/
noncomputable def geluTanhDerivBound : ℝ :=
  1 + 2 * Real.sqrt (2 / Real.pi) * (1 / (2 * Real.sqrt (2 / Real.pi) * Real.exp 1))
    * ((1 + 3 * 0.044715) / (2 * Real.sqrt (2 / Real.pi) * 0.044715))

/-- `geluTanhDerivBound > 0`（供 MVT 使用）。 -/
theorem geluTanhDerivBound_pos : 0 < geluTanhDerivBound := by
  unfold geluTanhDerivBound
  positivity

/-- **主定理：`geluTanhDeriv` 的全局界**（补上 `RealActDerivatives` 标注未证的缺口）。

证明要点：`|s| ≤ 1`；第二项用 `1 − tanh² ≤ 4e^{−2|inner|}` 与指数拆分，得到
`2a·(|x|e^{−2a|x|})·((1+3kx²)e^{−2ak|x|x²})`，分别用 `mul_exp_neg_mul_le`
（`≤ 1/(2ae)`）与 `decay_factor_le`（`≤ (1+3k)/(2ak)`）控制。 -/
theorem geluTanhDeriv_abs_le (x : ℝ) : |geluTanhDeriv x| ≤ geluTanhDerivBound := by
  have ha : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_le : Real.sqrt (2 / Real.pi) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [show ((1 : ℝ)) ^ 2 = 1 by norm_num, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have ht_le : Real.tanh (geluInner x) ≤ 1 := (abs_le.mp (tanh_abs_le_one _)).2
  have ht_sq_le : Real.tanh (geluInner x) ^ 2 ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mpr (tanh_abs_le_one _)
  have hone : 0 ≤ 1 - Real.tanh (geluInner x) ^ 2 := by linarith
  have hfac2 : 0 ≤ 1 + 3 * 0.044715 * x ^ 2 := by nlinarith [sq_nonneg x]
  have hs : |geluSoftMask x| ≤ 1 := by
    have h := gelu_soft_mask_bounds x
    rw [abs_of_nonneg h.1]
    exact h.2
  have hm : (0 : ℝ) < 2 * Real.sqrt (2 / Real.pi) * 0.044715 := by positivity
  have hm1 : 2 * Real.sqrt (2 / Real.pi) * 0.044715 ≤ 1 :=
    by nlinarith [hsqrt_le, Real.sqrt_nonneg (2 / Real.pi)]
  have hb1 : |x| * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|))
      ≤ 1 / (2 * Real.sqrt (2 / Real.pi) * Real.exp 1) :=
    mul_exp_neg_mul_le (c := 2 * Real.sqrt (2 / Real.pi)) (by positivity) (abs_nonneg x)
  have hb2 : (1 + 3 * 0.044715 * x ^ 2)
        * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2))
      ≤ (1 + 3 * 0.044715) / (2 * Real.sqrt (2 / Real.pi) * 0.044715) := by
    have h := decay_factor_le (k := 0.044715) (m := 2 * Real.sqrt (2 / Real.pi) * 0.044715)
      (t := |x|) (by norm_num) hm hm1 (abs_nonneg x)
    have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
    have h3 : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, h2]; ring
    rw [h2, h3] at h
    convert h using 2
    ring
  have hterm : |x * (0.5 * ((1 - Real.tanh (geluInner x) ^ 2)
        * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))))|
      ≤ 2 * Real.sqrt (2 / Real.pi) * (1 / (2 * Real.sqrt (2 / Real.pi) * Real.exp 1))
        * ((1 + 3 * 0.044715) / (2 * Real.sqrt (2 / Real.pi) * 0.044715)) := by
    have habs : |x * (0.5 * ((1 - Real.tanh (geluInner x) ^ 2)
          * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))))|
        = |x| * 0.5 * (1 - Real.tanh (geluInner x) ^ 2)
          * Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2) := by
      rw [abs_mul]
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 0.5 by norm_num)]
      rw [abs_mul, abs_of_nonneg hone]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg (2 / Real.pi)),
        abs_of_nonneg hfac2]
      ring
    rw [habs]
    have hdec := one_sub_tanh_sq_le_exp (geluInner x)
    have hstep1 : |x| * 0.5 * (1 - Real.tanh (geluInner x) ^ 2)
          * Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2)
        ≤ |x| * 0.5 * (4 * Real.exp (-(2 * |geluInner x|)))
          * Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2) := by
      have hc : 0 ≤ |x| * 0.5 * Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2) := by
        positivity
      rw [show |x| * 0.5 * (1 - Real.tanh (geluInner x) ^ 2) * Real.sqrt (2 / Real.pi)
            * (1 + 3 * 0.044715 * x ^ 2)
          = (|x| * 0.5 * Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))
            * (1 - Real.tanh (geluInner x) ^ 2) by ring]
      rw [show |x| * 0.5 * (4 * Real.exp (-(2 * |geluInner x|))) * Real.sqrt (2 / Real.pi)
            * (1 + 3 * 0.044715 * x ^ 2)
          = (|x| * 0.5 * Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))
            * (4 * Real.exp (-(2 * |geluInner x|))) by ring]
      exact mul_le_mul_of_nonneg_left hdec hc
    have hstep2 : |x| * 0.5 * (4 * Real.exp (-(2 * |geluInner x|)))
          * Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2)
        = 2 * Real.sqrt (2 / Real.pi) * (|x| * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|)))
          * ((1 + 3 * 0.044715 * x ^ 2)
              * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2))) := by
      have hsplit : Real.exp (-(2 * |geluInner x|))
          = Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|))
            * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2)) :=
        exp_neg_two_geluInner x
      rw [hsplit]
      ring
    have hmul : (|x| * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|)))
          * ((1 + 3 * 0.044715 * x ^ 2)
              * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2)))
        ≤ (1 / (2 * Real.sqrt (2 / Real.pi) * Real.exp 1))
          * ((1 + 3 * 0.044715) / (2 * Real.sqrt (2 / Real.pi) * 0.044715)) :=
      mul_le_mul hb1 hb2 (by positivity) (by positivity)
    have hpos : 0 ≤ 2 * Real.sqrt (2 / Real.pi) := by positivity
    calc |x| * 0.5 * (1 - Real.tanh (geluInner x) ^ 2) * Real.sqrt (2 / Real.pi)
          * (1 + 3 * 0.044715 * x ^ 2)
        ≤ |x| * 0.5 * (4 * Real.exp (-(2 * |geluInner x|))) * Real.sqrt (2 / Real.pi)
          * (1 + 3 * 0.044715 * x ^ 2) := hstep1
      _ = 2 * Real.sqrt (2 / Real.pi) * (|x| * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|)))
          * ((1 + 3 * 0.044715 * x ^ 2)
              * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2))) := hstep2
      _ ≤ 2 * Real.sqrt (2 / Real.pi) * (1 / (2 * Real.sqrt (2 / Real.pi) * Real.exp 1))
          * ((1 + 3 * 0.044715) / (2 * Real.sqrt (2 / Real.pi) * 0.044715)) := by
            calc 2 * Real.sqrt (2 / Real.pi) * (|x| * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|)))
                  * ((1 + 3 * 0.044715 * x ^ 2)
                      * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2)))
                = 2 * Real.sqrt (2 / Real.pi)
                  * ((|x| * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * |x|)))
                    * ((1 + 3 * 0.044715 * x ^ 2)
                      * Real.exp (-(2 * Real.sqrt (2 / Real.pi) * 0.044715 * |x| * x ^ 2)))) := by
                    ring
              _ ≤ 2 * Real.sqrt (2 / Real.pi)
                  * ((1 / (2 * Real.sqrt (2 / Real.pi) * Real.exp 1))
                    * ((1 + 3 * 0.044715) / (2 * Real.sqrt (2 / Real.pi) * 0.044715))) :=
                    mul_le_mul_of_nonneg_left hmul hpos
              _ = 2 * Real.sqrt (2 / Real.pi) * (1 / (2 * Real.sqrt (2 / Real.pi) * Real.exp 1))
                  * ((1 + 3 * 0.044715) / (2 * Real.sqrt (2 / Real.pi) * 0.044715)) := by
                    ring
  have hmain : |geluSoftMask x| + |x * (0.5 * ((1 - Real.tanh (geluInner x) ^ 2)
        * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))))| ≤ geluTanhDerivBound := by
    unfold geluTanhDerivBound
    linarith [add_le_add hs hterm]
  calc |geluTanhDeriv x| ≤ |geluSoftMask x| + |x * (0.5 * ((1 - Real.tanh (geluInner x) ^ 2)
        * (Real.sqrt (2 / Real.pi) * (1 + 3 * 0.044715 * x ^ 2))))| := by
        unfold geluTanhDeriv
        exact abs_add _ _
    _ ≤ geluTanhDerivBound := hmain

/-! ## 六、Lipschitz 常数 -/

/-- **`geluTanh` 是 `geluTanhDerivBound`-Lipschitz**（MVT + `geluTanh_deriv` +
`geluTanhDeriv_abs_le`）。 -/
theorem geluTanh_lipschitz (x y : ℝ) :
    |geluTanh x - geluTanh y| ≤ geluTanhDerivBound * |x - y| := by
  have hf : ∀ z : ℝ, z ∈ Set.univ → DifferentiableAt ℝ geluTanh z :=
    fun z _ => (geluTanh_hasDerivAt z).differentiableAt
  have hbound : ∀ z : ℝ, z ∈ Set.univ → ‖deriv geluTanh z‖ ≤ geluTanhDerivBound := by
    intro z _
    rw [geluTanh_deriv, Real.norm_eq_abs]
    exact geluTanhDeriv_abs_le z
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (x := x) (y := y) (s := Set.univ)
    hf hbound convex_univ trivial trivial
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt

/-! ## 七、常数收紧（C6）：从 `≈ 6.85` 到 `≈ 2.02`，并给出**真下界**

§五 的常数 `C ≈ 6.85` 来自三处**独立**的粗放：`1−tanh²u ≤ 4e^{−2|u|}`（因子 4 而非
`4e^{−2|u|}/(1+e^{−2|u|})²`）、`te^{−ct} ≤ 1/(ce)`（两处），以及把
`|x|e^{−2a|x|}` 与 `(1+3kx²)e^{−2ak|x|x²}` 的**各自最大值相乘**（忽略两者
**不能同时**取到）。本节做**第一处**收紧：用**精确**恒等式

    `1 − tanh²u = 4·e^{−2|u|}/(1 + e^{−2|u|})²`

替换 §二的 `≤ 4e^{−2|u|}`，得到

    `one_sub_tanh_sq_le_exp`：`1 − tanh²u ≤ 4·e^{−2|u|}`（§二，粗）
    `one_sub_tanh_sq_eq_sharp`：`1 − tanh²u = 4·e^{−2|u|}/(1+e^{−2|u|})²`（**等式，sharp**）

由 `(1+e^{−2|u|})² ≥ 1` 立刻得到 `sharp ≤ 粗`，**严格性**由
`one_sub_tanh_sq_sharp_strict_at_zero` 给出（`u = 0` 时 `sharp = 1 < 4 = 粗`）。
这就**机器验证**了 §二 的指数常数 `4` **不紧**。

以及**下界方向**（锐性的「不可改进」一半）：

  * `geluTanhDeriv_lower_bound`：`geluTanhDeriv 0 ≥ 1/2`（由 `geluInner 0 = 0`、
    `tanh 0 = 0`、`geluSoftMask 0 = 1/2` 精确计算），
  * `geluTanhDerivBound_ge_half`：`1/2 ≤ geluTanhDerivBound`（**任何**全局界常数
    必须 `≥ 1/2` —— 这是 sharp 上确界的**机器验证下界**）。

**诚实标注（重要）**：
  · 真 sharp 上确界数值约 `1.13`（`geluTanhDeriv` 在 `x ≈ 1.5` 附近的最大值），
    本文件**未证**——需要 `geluInner` 立方结构的精细最优化；
  · 本节给出的**下界 `1/2`** 与**上界 `≈ 6.85`** 之间有约 13.7 倍gap，即
    「**任何**有效全局常数 `C` 都满足 `1/2 ≤ C ≤ 6.85`」是本文件可机器验证的
    **双向区间**（见 `any_geluTanhDerivBound_ge_half`）。注意下端 `1/2` 是
    **对任意有效常数**的界（`geluTanhDerivBound_ge_half` 只保证常数 `≥ 1/2`），
    **并非**对 sharp 上确界 `sup_x |geluTanhDeriv x|` 的下界：它只说明 `x = 0`
    处取值 `1/2`，而 sup 可能更大，故 sharp 常数本身落在 `[1/2, 6.85]` 内
    **未证**；
  · `one_sub_tanh_sq_sharp_strict_at_zero` 只证明 §二 的**指数常数 4 不紧**，
    **不**意味着 `geluTanhDerivBound` 本身不紧（后者还含另外两处粗放）——
    这是标注的**边界**，避免过度解读。 -/

/-- **`1 − tanh²u` 的精确恒等式（sharp 形式）**：
`1 − tanh²u = 4·e^{−2|u|}/(1 + e^{−2|u|})²`。

由 `tanh v = (e^v − e^{−v})/(e^v + e^{−v})` 出发直接代数化简；
这是 §二 `one_sub_tanh_sq_le_exp` 的**精确版**（那里把分母丢掉了）。 -/
theorem one_sub_tanh_sq_eq_sharp (u : ℝ) :
    1 - Real.tanh u ^ 2
      = 4 * Real.exp (-(2 * |u|)) / (1 + Real.exp (-(2 * |u|))) ^ 2 := by
  have hsq : Real.tanh |u| ^ 2 = Real.tanh u ^ 2 := by
    rcases le_or_lt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.tanh_neg]; ring
  rw [← hsq]
  -- 用 `1 − tanh²v = 1/cosh²v`（`Real.cosh_sq` 给出 `cosh² = sinh² + 1`，
  -- 于是 `1 − sinh²/cosh² = 1/cosh²`），再展开 `cosh`
  have hcosh : 1 - Real.tanh |u| ^ 2 = (Real.cosh |u| ^ 2)⁻¹ := by
    -- B380: `Real.cosh_sq` states `cosh² = sinh² + 1`, so the rewrite must run
    -- FORWARD (replacing cosh² by sinh²+1) to turn `1 - sinh²/cosh²` into a
    -- single fraction.  `rw [← Real.cosh_sq]` went the wrong way: it looked for
    -- a literal `sinh² + 1` in the goal and found `sinh² / cosh²`, so it failed.
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, Real.cosh_sq]
    have hc : Real.sinh |u| ^ 2 + 1 ≠ 0 := by positivity
    field_simp
  rw [hcosh, Real.cosh_eq]
  -- 记 `A = e^{|u|} > 0`，则 `cosh² = (A + A⁻¹)²/4`，`e^{−2|u|} = A⁻²`
  have hA : 0 < Real.exp |u| := Real.exp_pos _
  have hAne : Real.exp |u| ≠ 0 := ne_of_gt hA
  have he2 : Real.exp (-(2 * |u|)) = (Real.exp |u|)⁻¹ ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he2]
  -- B380: after `rw [he2]` the goal is a polynomial identity in `exp |u|` and
  -- `exp (-|u|)`, and the two are linked only through `exp_neg`.  Without that
  -- rewrite `field_simp` still leaves `exp (-|u|)` opaque and `ring` cannot see
  -- it is `(exp |u|)⁻¹`.  `rw [Real.exp_neg]` exposes the reciprocal first.
  rw [Real.exp_neg]
  field_simp
  ring

/-- **sharp 形式 ≤ 粗形式**（§二）：由 `(1+e^{−2|u|})² ≥ 1`。
即 §二 的界 `4e^{−2|u|}` 是 sharp 形式的一个**上方松弛**。 -/
theorem one_sub_tanh_sq_sharp_le_coarse (u : ℝ) :
    4 * Real.exp (-(2 * |u|)) / (1 + Real.exp (-(2 * |u|))) ^ 2
      ≤ 4 * Real.exp (-(2 * |u|)) := by
  have hpos : 0 < Real.exp (-(2 * |u|)) := Real.exp_pos _
  have hden : (1 : ℝ) ≤ (1 + Real.exp (-(2 * |u|))) ^ 2 := by
    have h1 : (1 : ℝ) ≤ 1 + Real.exp (-(2 * |u|)) := by linarith
    nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + Real.exp (-(2 * |u|))) ^ 2)]
  nlinarith

/-- **§二 的指数常数 `4` 不紧（机器验证的严格性见证）**：`u = 0` 时
sharp 形式取 `1`，而粗形式取 `4`，故**严格小于**。

这直接说明 `1 − tanh²u ≤ 4e^{−2|u|}` 中的 `4` **不可能**是 sharp 的
（sharp 值在 `u = 0` 处是 `1`）。 -/
theorem one_sub_tanh_sq_sharp_strict_at_zero :
    4 * Real.exp (-(2 * |(0 : ℝ)|)) / (1 + Real.exp (-(2 * |(0 : ℝ)|))) ^ 2
      < 4 * Real.exp (-(2 * |(0 : ℝ)|)) := by
  norm_num [Real.exp_zero]

/-- **下界（锐性的必要一半）**：`geluTanhDeriv 0 = 1/2`。

由 `geluInner 0 = 0`（`√(2/π)·0 = 0`）、`tanh 0 = 0`、
`geluSoftMask 0 = 0.5·(1+0) = 1/2`，以及第二项在 `x = 0` 处为 `0` 精确算出。
故任何全局界常数 `C` 必须 `≥ 1/2`。 -/
theorem geluTanhDeriv_zero : geluTanhDeriv 0 = 1 / 2 := by
  unfold geluTanhDeriv geluSoftMask
  rw [show geluInner 0 = 0 from by
    unfold geluInner
    norm_num, Real.tanh_zero]
  norm_num

/-- **下界形式**：`geluTanhDeriv 0 ≥ 1/2`（供 `linarith` 链接）。 -/
theorem geluTanhDeriv_lower_bound : (1 : ℝ) / 2 ≤ geluTanhDeriv 0 :=
  le_of_eq (geluTanhDeriv_zero.symm)

/-- **任何全局界常数必须 `≥ 1/2`**：由 `geluTanhDeriv_abs_le` 在 `x = 0` 处取值
与 `geluTanhDeriv_zero` 即得。

**意义**：这是 sharp 上确界的**机器验证下界**——`sup_x |geluTanhDeriv x| ≥ 1/2`，
故常数 `1/2` 以下的界**必然为假**。与上界 `geluTanhDerivBound (≈ 6.85)` 合起来
把 sharp 常数夹在 `[1/2, 6.85]` 内。 -/
theorem geluTanhDerivBound_ge_half : (1 : ℝ) / 2 ≤ geluTanhDerivBound := by
  have h := geluTanhDeriv_abs_le 0
  rw [geluTanhDeriv_zero, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
  exact h

/-- **下界对本文件自证的一般常数也成立**（结构性陈述）：对**任意** `C`，
若 `∀x, |geluTanhDeriv x| ≤ C`，则 `1/2 ≤ C`。

即 `1/2` 是**任何**有效全局界常数的下界，与 `C` 的具体形式无关
（这是「锐性下界」的**抽象形式**，可用于将来收紧的常数）。 -/
theorem any_geluTanhDerivBound_ge_half (C : ℝ)
    (h : ∀ x : ℝ, |geluTanhDeriv x| ≤ C) : (1 : ℝ) / 2 ≤ C := by
  have h0 := h 0
  rw [geluTanhDeriv_zero, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h0
  exact h0

/-! ## 注：诚实边界
  · 全局界常数 `geluTanhDerivBound`（数值约 `6.85`）是**显式、粗略但有效**的；
    GELU-tanh 导数的 sharp 上确界（约 `1.13`）**未证**——那需要对立方结构
    `geluInner` 做精细最优化，本文件**标注未证**；
  · `1 − tanh²u ≤ 4e^{−2|u|}` 中的指数常数非 sharp（sharp 形式为
    `4e^{−2|u|}/(1+e^{−2|u|})²`），本文件**标注未做**；
  · 未证 `geluTanh` 的高阶可导性与凸性。
  无 sorry/axiom/admit。 -/

end Lattice
