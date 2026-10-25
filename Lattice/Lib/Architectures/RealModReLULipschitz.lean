import Mathlib
import Lattice.Lib.Architectures.RealModReLU
import Lattice.Lift.RealNonlinear
/-!
# LATTICE: modReLU 的 1-Lipschitz（`b ≤ 0`）与 `b > 0` 的机器验证反例

`RealModReLU` 的 docstring **明确标注**未证 modReLU 的 1-Lipschitz
（`|modReLU b z − modReLU b w| ≤ |z − w|`），只给了幅度上界
`|modReLU b z| ≤ |z| + |b|`。本文件澄清这条命题的**真实真值**：

  * **`b > 0` 时命题是假的**（`modReLU_not_one_lipschitz_for_pos_bias`）——
    `z = 0` 与 `w = 1/2` 给出 `|modReLU 1 0 − modReLU 1 (1/2)| = 3/2 > 1/2 = |0 − 1/2|`
    （偏置 `b > 0` 使 `modReLU` 在 `0` 处**不连续**：方向相关的非零极限对上了
    约定的 `modReLU b 0 = 0`）。这是**机器验证的反例**；
  * **`b ≤ 0` 时命题成立**（`modReLU_lipschitz_of_nonpos`）——此时 modReLU 是
    「极坐标软阈值」`z ↦ max(0, |z|−c)·z/|z|`（`c = −b ≥ 0`），是 1-Lipschitz 的。

**`b ≤ 0` 的证明路线**（比直接算 `normSq` 更省力，只用到 `Complex.abs` 的乘法性）：
记 `c = −b ≥ 0`，`λ(z) = relu(|z|+b)/|z|`（`z ≠ 0`）。则
`|λ(z)| ≤ 1`、`(1−λ(z)) = c/|z|`（当 `|z| ≥ c`）、且
`|λ(z) − λ(w)| ≤ c·|z−w|/(|z|·|w|)`。分解
`λ(z) z − λ(w) w = λ(z)(z−w) + (λ(z)−λ(w)) w` 后：
  * `|z|, |w| ≥ c`：`≤ (1−c/|z|)|z−w| + (c/|z|)|z−w| = |z−w|`；
  * `|z| < c`：`λ(z) = 0`，`≤ λ(w)|w| ≤ |w|−c ≤ |w|−|z| ≤ |z−w|`。

**诚实标注（中文关键词）**：
  · `b > 0` 的反例是**精确**结论（推翻原命题，按铁律给机器验证反例）；
  · `b ≤ 0` 的 1-Lipschitz 是**完整**证明（无特例假设、无额外假设）；
  · **降级说明**：原任务书的「全 `b` 的 1-Lipschitz」**不可能**成立（见反例），
    因此本文件把它**降级**为「`b ≤ 0` 成立 + `b > 0` 反例」这一正确的二分解；
  · 未证 `b > 0` 时 modReLU 在 `0` 处的连续性（反例已说明不连续）。
  无 sorry/axiom/admit。
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace Lattice

/-! ## 一、`b > 0` 的机器验证反例 -/

/-- `relu` 的 1-Lipschitz 性（`|relu a − relu b| ≤ |a − b|`，`max` 的 1-Lipschitz）。 -/
theorem relu_abs_sub_le (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  exact abs_max_sub_max_le_abs a b 0

/-- 具体值：`modReLU 1 (1/2) = 3/2`（实数意义下，`b = 1 > 0`）。 -/
theorem modReLU_one_half :
    modReLU 1 (((1 / 2 : ℝ)) : ℂ) = (((3 / 2 : ℝ)) : ℂ) := by
  have hz : (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by norm_num
  rw [modReLU_phase_preserved 1 _ hz]
  have habs : Complex.abs ((((1 / 2 : ℝ)) : ℂ)) = (1 / 2 : ℝ) := by
    rw [Complex.abs_ofReal]
    norm_num
  have hr : relu (Complex.abs ((((1 / 2 : ℝ)) : ℂ)) + 1) = (3 / 2 : ℝ) := by
    rw [habs]
    unfold relu
    norm_num
  rw [hr, habs]
  norm_num

/-- **反例（精确）**：`b = 1`、`z = 0`、`w = 1/2` 时
`|modReLU 1 0 − modReLU 1 (1/2)| = 3/2 > 1/2 = |0 − 1/2|`。 -/
theorem modReLU_counterexample :
    Complex.abs (modReLU 1 0 - modReLU 1 (((1 / 2 : ℝ)) : ℂ)) = 3 / 2 ∧
    Complex.abs ((0 : ℂ) - (((1 / 2 : ℝ)) : ℂ)) = 1 / 2 := by
  constructor
  · rw [modReLU_zero, zero_sub, modReLU_one_half]
    rw [← Complex.ofReal_neg, Complex.abs_ofReal]
    norm_num
  · rw [show (0 : ℂ) - (((1 / 2 : ℝ)) : ℂ) = (((-(1 / 2) : ℝ)) : ℂ) by norm_num]
    rw [Complex.abs_ofReal]
    norm_num

/-- **原命题（全 `b` 的 1-Lipschitz）为假**（对 `b = 1` 即被上面的具体反例推翻）。 -/
theorem modReLU_not_one_lipschitz_for_pos_bias :
    ¬ (∀ (b : ℝ) (z w : ℂ),
        Complex.abs (modReLU b z - modReLU b w) ≤ Complex.abs (z - w)) := by
  intro h
  have h1 := h 1 0 (((1 / 2 : ℝ)) : ℂ)
  rw [modReLU_counterexample.1, modReLU_counterexample.2] at h1
  norm_num at h1

/-! ## 二、`b ≤ 0` 的 1-Lipschitz -/

/-- 门增益 `λ(z) = relu(|z| + b)/|z|`（`z = 0` 时分母为 0，但 `modReLU` 约定为 0，
本定义只在 `z ≠ 0` 时使用）。 -/
def modGain (b : ℝ) (z : ℂ) : ℝ := relu (Complex.abs z + b) / Complex.abs z

/-- 相位保持的增益形式（`z ≠ 0`）：`modReLU b z = ↑(modGain b z) · z`。 -/
theorem modReLU_eq_gain_mul (b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    modReLU b z = ((modGain b z : ℝ) : ℂ) * z := by
  rw [modReLU_phase_preserved b z hz]
  rfl

/-- `relu x = x`（`x ≥ 0`）。 -/
lemma relu_of_nonneg {x : ℝ} (h : 0 ≤ x) : relu x = x := by
  unfold relu
  exact max_eq_left h

/-- **主定理：`b ≤ 0` 时 modReLU 是 1-Lipschitz**。证明见模块 docstring 的路线。 -/
theorem modReLU_lipschitz_of_nonpos (b : ℝ) (hb : b ≤ 0) (z w : ℂ) :
    Complex.abs (modReLU b z - modReLU b w) ≤ Complex.abs (z - w) := by
  set c : ℝ := -b with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have htb : ∀ t : ℂ, Complex.abs t + b = Complex.abs t - c := by
    intro t
    rw [hc]
    ring
  -- 反向三角不等式：|‖z‖ − ‖w‖| ≤ ‖z − w‖
  have hrev : |Complex.abs z - Complex.abs w| ≤ Complex.abs (z - w) := by
    simpa only [← Complex.norm_eq_abs] using abs_norm_sub_norm_le z w
  by_cases hz : z = 0
  · subst hz
    rw [modReLU_zero, zero_sub]
    rw [show Complex.abs (-(modReLU b w)) = Complex.abs (modReLU b w) from
      Complex.abs.map_neg (modReLU b w)]
    rw [show Complex.abs ((0 : ℂ) - w) = Complex.abs w from by
      rw [zero_sub, Complex.abs.map_neg]]
    by_cases hw : w = 0
    · subst hw
      rw [modReLU_zero]
    · rw [modReLU_magnitude b w hw, htb w]
      exact max_le (by linarith [hc0]) (Complex.abs.nonneg w)
  · by_cases hw : w = 0
    · subst hw
      rw [modReLU_zero]
      simp only [sub_zero]
      rw [modReLU_magnitude b z hz, htb z]
      exact max_le (by linarith [hc0]) (Complex.abs.nonneg z)
    · -- z ≠ 0 且 w ≠ 0
      have hrz : 0 < Complex.abs z := by
        rw [← Complex.norm_eq_abs]
        exact norm_pos_iff.mpr hz
      have hrw : 0 < Complex.abs w := by
        rw [← Complex.norm_eq_abs]
        exact norm_pos_iff.mpr hw
      rcases le_or_lt (Complex.abs z) c with hzc | hzc
      · -- |z| ≤ c：modReLU b z = 0
        have hzneg : Complex.abs z - c ≤ 0 := by linarith
        have hrelu : relu (Complex.abs z + b) = 0 := by
          rw [htb z]
          unfold relu
          exact max_eq_right hzneg
        have hz0 : modReLU b z = 0 := by
          rw [modReLU_phase_preserved b z hz, hrelu]
          simp
        rw [hz0]
        rw [show (0 : ℂ) - modReLU b w = -(modReLU b w) from zero_sub _]
        rw [Complex.abs.map_neg (modReLU b w)]
        rw [modReLU_magnitude b w hw, htb w]
        rw [show relu (Complex.abs w - c) = max (Complex.abs w - c) 0 from rfl]
        refine max_le ?_ (Complex.abs.nonneg (z - w))
        calc Complex.abs w - c ≤ Complex.abs w - Complex.abs z := by linarith [hzc]
          _ ≤ |Complex.abs w - Complex.abs z| := le_abs_self _
          _ = |Complex.abs z - Complex.abs w| := abs_sub_comm _ _
          _ ≤ Complex.abs (z - w) := hrev
      · rcases le_or_lt (Complex.abs w) c with hwc | hwc
        · -- |w| ≤ c：modReLU b w = 0
          have hwneg : Complex.abs w - c ≤ 0 := by linarith
          have hreluw : relu (Complex.abs w + b) = 0 := by
            rw [htb w]
            unfold relu
            exact max_eq_right hwneg
          have hw0 : modReLU b w = 0 := by
            rw [modReLU_phase_preserved b w hw, hreluw]
            simp
          rw [hw0, sub_zero]
          rw [modReLU_magnitude b z hz, htb z]
          rw [show relu (Complex.abs z - c) = max (Complex.abs z - c) 0 from rfl]
          refine max_le ?_ (Complex.abs.nonneg (z - w))
          calc Complex.abs z - c ≤ Complex.abs z - Complex.abs w := by linarith [hwc]
            _ ≤ |Complex.abs z - Complex.abs w| := le_abs_self _
            _ ≤ Complex.abs (z - w) := hrev
        · -- |z| > c 且 |w| > c
          have hlamz : modGain b z = 1 - c / Complex.abs z := by
            unfold modGain
            rw [htb z]
            rw [relu_of_nonneg (x := Complex.abs z - c) (le_of_lt (sub_pos.mpr hzc)),
              sub_div, div_self (ne_of_gt hrz)]
          have hlamw : modGain b w = 1 - c / Complex.abs w := by
            unfold modGain
            rw [htb w]
            rw [relu_of_nonneg (x := Complex.abs w - c) (le_of_lt (sub_pos.mpr hwc)),
              sub_div, div_self (ne_of_gt hrw)]
          have hlamzpos : 0 ≤ modGain b z := by
            rw [hlamz]
            have h1 : c / Complex.abs z ≤ 1 := by
              rw [div_le_one hrz]
              exact le_of_lt hzc
            linarith
          -- 分解与三角不等式
          have hdecomp : modReLU b z - modReLU b w
              = ((modGain b z : ℝ) : ℂ) * (z - w)
                + (((modGain b z : ℝ) : ℂ) - ((modGain b w : ℝ) : ℂ)) * w := by
            rw [modReLU_eq_gain_mul b z hz, modReLU_eq_gain_mul b w hw]
            ring
          have htri : Complex.abs (modReLU b z - modReLU b w)
              ≤ modGain b z * Complex.abs (z - w)
                + |modGain b z - modGain b w| * Complex.abs w := by
            rw [hdecomp]
            calc Complex.abs (((modGain b z : ℝ) : ℂ) * (z - w)
                  + (((modGain b z : ℝ) : ℂ) - ((modGain b w : ℝ) : ℂ)) * w)
                ≤ Complex.abs (((modGain b z : ℝ) : ℂ) * (z - w))
                  + Complex.abs ((((modGain b z : ℝ) : ℂ) - ((modGain b w : ℝ) : ℂ)) * w) :=
                  AbsoluteValue.add_le Complex.abs _ _
              _ = modGain b z * Complex.abs (z - w)
                  + Complex.abs (((modGain b z : ℝ) : ℂ) - ((modGain b w : ℝ) : ℂ))
                    * Complex.abs w := by
                  rw [Complex.abs.map_mul, Complex.abs.map_mul, Complex.abs_ofReal,
                    abs_of_nonneg hlamzpos]
              _ = modGain b z * Complex.abs (z - w)
                  + |modGain b z - modGain b w| * Complex.abs w := by
                  rw [← Complex.ofReal_sub, Complex.abs_ofReal]
          -- 增益差的界
          have hlamdiff : |modGain b z - modGain b w|
              ≤ c * Complex.abs (z - w) / (Complex.abs z * Complex.abs w) := by
            have hEq : (1 - c / Complex.abs z) - (1 - c / Complex.abs w)
                = c * (Complex.abs z - Complex.abs w) / (Complex.abs z * Complex.abs w) := by
              rw [show (1 - c / Complex.abs z) - (1 - c / Complex.abs w)
                    = c / Complex.abs w - c / Complex.abs z by ring]
              field_simp
              ring
            rw [hlamz, hlamw, hEq, abs_div, abs_mul, abs_of_nonneg hc0,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ Complex.abs z * Complex.abs w)]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrev hc0)
              (by positivity)
          -- 合并
          have hcombine : modGain b z * Complex.abs (z - w)
              + (c / Complex.abs z) * Complex.abs (z - w) = Complex.abs (z - w) := by
            rw [hlamz]
            ring
          calc Complex.abs (modReLU b z - modReLU b w)
              ≤ modGain b z * Complex.abs (z - w)
                + |modGain b z - modGain b w| * Complex.abs w := htri
            _ ≤ modGain b z * Complex.abs (z - w)
                + (c * Complex.abs (z - w) / (Complex.abs z * Complex.abs w))
                  * Complex.abs w := by
                have h1 : |modGain b z - modGain b w| * Complex.abs w
                    ≤ (c * Complex.abs (z - w) / (Complex.abs z * Complex.abs w))
                      * Complex.abs w :=
                  mul_le_mul_of_nonneg_right hlamdiff (Complex.abs.nonneg w)
                linarith
            _ = modGain b z * Complex.abs (z - w)
                + (c / Complex.abs z) * Complex.abs (z - w) := by
                field_simp [ne_of_gt hrw]
                ring
            _ = Complex.abs (z - w) := hcombine

/-! ## 注：诚实边界
  · **`b > 0` 时 1-Lipschitz 为假**（`modReLU_not_one_lipschitz_for_pos_bias`，
    机器验证反例 `z = 0`、`w = 1/2`、`b = 1`）——原 `RealModReLU` 的标注
    「未证」其实可以加强为「**不成立**」；
  · **`b ≤ 0` 时 1-Lipschitz 成立**，本文件给出完整证明（无特例限制）；
  · 因此本文件把原任务书的「全 `b` 的 1-Lipschitz」**降级**为正确的二分：
    `b ≤ 0` 定理 + `b > 0` 反例（**诚实降级/标注**）；
  · 未做：`b > 0` 时 modReLU 的连续性研究（反例已说明在 `0` 处不连续）。
  无 sorry/axiom/admit。 -/

end Lattice
