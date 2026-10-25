import Mathlib

/-!
# LATTICE: Adam 优化器（一维标量版）—— 步长有界性与偏差修正

RealSGD 给出动量（重球法）二阶递推；本文件给出 **Adam** 优化器的
一维（标量）稳定核心：一阶矩、二阶矩与自适应步长

    m' = β₁·m + (1 - β₁)·g
    v' = β₂·v + (1 - β₂)·g²
    x' = x - η·m' / (√v' + ε)

Adam = 动量（一阶矩指数滑动平均）+ RMSProp（二阶矩指数滑动平均）+ 偏差修正。
本文件证明的是 Adam **本身的代数与有界结构**（不涉及随机性）：

  1. adam_v_nonneg：0 ≤ β₂ ≤ 1，v ≥ 0 ⟹ v' ≥ 0（二阶矩非负）；
  2. adam_denominator_pos：√v' + ε > 0（v' ≥ 0，ε > 0）—— 自适应步长分母严格正；
  3. adam_step_abs_le_eta：|x' - x| ≤ η·|m'| / ε —— 步长由 η、|m'| 与 ε **统一控制**
     （分母 √v' + ε ≥ ε，故自适应归一化不会放大步长）；
  4. adam_moment_bound：0 ≤ β₁ ≤ 1，|g_t| ≤ B（全部 t），|m_0| = 0 ⟹
     |m_n| ≤ (1 - β₁ⁿ)·B —— 一阶矩的**未修正**衰减界；
  5. adam_bias_correction：0 ≤ β₁ < 1，n ≠ 0 ⟹ |m_n / (1 - β₁ⁿ)| ≤ B ——
     偏差修正后的矩估计落在梯度界内（这正是 Adam 偏差修正的动机：修正因子
     (1 - β₁ⁿ) 恰好补偿初始零矩造成的向下偏置）；
  6. adam_step_bounded_learning：|m| ≤ B 且 |g| ≤ B ⟹ |x' - x| ≤ η·B/ε ——
     全局步长上界（全局收敛的前提条件之一）。

诚实边界（重要）：
  · 本文件只给 **一步界的结构 + 有限步矩估计界**，即 Adam 的「步长有界性」；
  · **完整 Adam 收敛定理（Kingma & Ba 2015，O(1/√T) 遗憾界）** 需要随机梯度
    的无偏性、有界方差、凸性（或梯度有界下的在线学习框架）以及
    β₁,β₂ 的衰减调度等额外假设，超出本文件的确定性标量范围，标注为后续工作；
  · 全程无 sorry/axiom/admit；唯一假设是参数范围（0 ≤ β ≤ 1、ε > 0）与梯度界 B。
-/

noncomputable section

namespace Lattice

/-! ## 一阶矩 / 二阶矩 / Adam 更新 -/

/-- 一阶矩（动量）的指数滑动平均步：m' = β₁·m + (1 - β₁)·g。-/
def AdamM (β₁ : ℝ) (g m : ℝ) : ℝ := β₁ * m + (1 - β₁) * g

/-- 二阶矩的指数滑动平均步：v' = β₂·v + (1 - β₂)·g²。-/
def AdamV (β₂ : ℝ) (g v : ℝ) : ℝ := β₂ * v + (1 - β₂) * g ^ 2

/-- Adam 一步更新：x' = x - η·m' / (√v' + ε)。-/
def AdamUpdate (β₁ β₂ η ε g x m v : ℝ) : ℝ :=
  x - η * AdamM β₁ g m / (Real.sqrt (AdamV β₂ g v) + ε)

/-! ## 定理一：二阶矩非负 -/

theorem adam_v_nonneg (β₂ g v : ℝ) (hβ₂0 : 0 ≤ β₂) (hβ₂1 : β₂ ≤ 1) (hv : 0 ≤ v) :
    0 ≤ AdamV β₂ g v := by
  unfold AdamV
  have h1 : 0 ≤ β₂ * v := mul_nonneg hβ₂0 hv
  have h2 : 0 ≤ (1 - β₂) * g ^ 2 := mul_nonneg (by linarith) (sq_nonneg g)
  linarith

/-! ## 定理二：自适应分母严格正 -/

theorem adam_denominator_pos (β₂ ε g v : ℝ) (_hβ₂0 : 0 ≤ β₂) (_hβ₂1 : β₂ ≤ 1)
    (_hv : 0 ≤ v) (hε : 0 < ε) :
    0 < Real.sqrt (AdamV β₂ g v) + ε :=
  add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hε

/-- 分母下界：√v' + ε ≥ ε（自适应归一化不放大步长）。-/
theorem adam_denominator_ge_eps (β₂ ε g v : ℝ) :
    ε ≤ Real.sqrt (AdamV β₂ g v) + ε :=
  le_add_of_nonneg_left (Real.sqrt_nonneg _)

/-! ## 定理三：单步位移的 η-界（核心）
|x' - x| ≤ η·|m'|/ε：自适应分母被 ε 从下方控制，故步长不会超过 η·|m'|/ε。-/

theorem adam_step_abs_le_eta (β₁ β₂ η ε g x m v : ℝ)
    (hη : 0 ≤ η) (hε : 0 < ε)
    (hβ₂0 : 0 ≤ β₂) (hβ₂1 : β₂ ≤ 1) (hv : 0 ≤ v) :
    |AdamUpdate β₁ β₂ η ε g x m v - x| ≤ η * |AdamM β₁ g m| / ε := by
  have hden : 0 < Real.sqrt (AdamV β₂ g v) + ε :=
    adam_denominator_pos β₂ ε g v hβ₂0 hβ₂1 hv hε
  have hge : ε ≤ Real.sqrt (AdamV β₂ g v) + ε := adam_denominator_ge_eps β₂ ε g v
  have hdiff : AdamUpdate β₁ β₂ η ε g x m v - x
      = -(η * AdamM β₁ g m / (Real.sqrt (AdamV β₂ g v) + ε)) := by
    unfold AdamUpdate
    ring
  have habs : |AdamUpdate β₁ β₂ η ε g x m v - x|
      = η * |AdamM β₁ g m| / (Real.sqrt (AdamV β₂ g v) + ε) := by
    rw [hdiff, abs_neg, abs_div, abs_mul, abs_of_nonneg hη, abs_of_pos hden]
  rw [habs]
  exact div_le_div_of_nonneg_left (mul_nonneg hη (abs_nonneg _)) hε hge

/-! ## 定理四：一阶矩步的单项界
0 ≤ β₁ ≤ 1，|m| ≤ B，|g| ≤ B ⟹ |m'| ≤ B（凸组合不越界）。-/

theorem adam_moment_step_bound (β₁ g m B : ℝ)
    (hβ₁0 : 0 ≤ β₁) (hβ₁1 : β₁ ≤ 1) (hm : |m| ≤ B) (hg : |g| ≤ B) :
    |AdamM β₁ g m| ≤ B := by
  have htri : |β₁ * m + (1 - β₁) * g| ≤ β₁ * |m| + (1 - β₁) * |g| := by
    calc
      |β₁ * m + (1 - β₁) * g| ≤ |β₁ * m| + |(1 - β₁) * g| := abs_add _ _
      _ = β₁ * |m| + (1 - β₁) * |g| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hβ₁0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - β₁)]
  have hmono : β₁ * |m| + (1 - β₁) * |g| ≤ β₁ * B + (1 - β₁) * B :=
    add_le_add (mul_le_mul_of_nonneg_left hm hβ₁0)
      (mul_le_mul_of_nonneg_left hg (by linarith))
  have hfin : β₁ * B + (1 - β₁) * B = B := by ring
  unfold AdamM
  linarith [le_trans htri hmono]

/-! ## 一阶矩与二阶矩的迭代序列 -/

/-- 一阶矩序列：m_0 = 0，m_{n+1} = β₁·m_n + (1 - β₁)·g_n。-/
def AdamMIter (β₁ : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => AdamM β₁ (g n) (AdamMIter β₁ g n)

/-- 二阶矩序列：v_0 = 0，v_{n+1} = β₂·v_n + (1 - β₂)·g_n²。-/
def AdamVIter (β₂ : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => AdamV β₂ (g n) (AdamVIter β₂ g n)

/-! ## 定理五：一阶矩的未修正界
0 ≤ β₁ ≤ 1，|g_t| ≤ B（全部 t），m_0 = 0 ⟹ |m_n| ≤ (1 - β₁ⁿ)·B。
这是「初始零矩 ⟹ 前期矩估计向下偏置」的定量形式。-/

theorem adam_moment_bound (β₁ B : ℝ) (g : ℕ → ℝ)
    (hβ₁0 : 0 ≤ β₁) (hβ₁1 : β₁ ≤ 1) (hB : 0 ≤ B) (hg : ∀ n, |g n| ≤ B) :
    ∀ n : ℕ, |AdamMIter β₁ g n| ≤ (1 - β₁ ^ n) * B := by
  intro n
  induction n with
  | zero =>
      simp [AdamMIter]
  | succ n ih =>
      have hstep : AdamMIter β₁ g (n + 1) = AdamM β₁ (g n) (AdamMIter β₁ g n) := rfl
      rw [hstep]
      calc
        |AdamM β₁ (g n) (AdamMIter β₁ g n)|
            ≤ β₁ * |AdamMIter β₁ g n| + (1 - β₁) * |g n| := by
              unfold AdamM
              calc
                |β₁ * AdamMIter β₁ g n + (1 - β₁) * g n|
                    ≤ |β₁ * AdamMIter β₁ g n| + |(1 - β₁) * g n| := abs_add _ _
                _ = β₁ * |AdamMIter β₁ g n| + (1 - β₁) * |g n| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hβ₁0,
                    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - β₁)]
        _ ≤ β₁ * ((1 - β₁ ^ n) * B) + (1 - β₁) * B :=
              add_le_add (mul_le_mul_of_nonneg_left ih hβ₁0)
                (mul_le_mul_of_nonneg_left (hg n) (by linarith))
        _ = (1 - β₁ ^ (n + 1)) * B := by
              rw [pow_succ]
              ring

/-! ## 定理六：偏差修正（核心）
0 ≤ β₁ < 1，n ≠ 0，|g_t| ≤ B ⟹ |m_n / (1 - β₁ⁿ)| ≤ B。
修正因子 1 - β₁ⁿ 恰好抵消初始零矩的向下偏置，使修正后的矩估计落在梯度界内。-/

theorem adam_bias_correction (β₁ B : ℝ) (g : ℕ → ℝ)
    (hβ₁0 : 0 ≤ β₁) (hβ₁1 : β₁ < 1) (hB : 0 ≤ B) (hg : ∀ n, |g n| ≤ B) :
    ∀ n : ℕ, n ≠ 0 → |AdamMIter β₁ g n / (1 - β₁ ^ n)| ≤ B := by
  intro n hn
  have hpow_lt : β₁ ^ n < 1 := pow_lt_one₀ hβ₁0 hβ₁1 hn
  have hden : 0 < 1 - β₁ ^ n := by linarith
  have hbound := adam_moment_bound β₁ B g hβ₁0 (le_of_lt hβ₁1) hB hg n
  rw [abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  nlinarith [hbound]

/-! ## 定理七：步长有界学习（加分）
|m| ≤ B 且 |g| ≤ B ⟹ |x' - x| ≤ η·B/ε：单步位移被 η·B/ε 全局控制，
这是「步长有界 ⟹ 迭代不会爆炸」的形式化前提（全局收敛的必要条件之一）。-/

theorem adam_step_bounded_learning (β₁ β₂ η ε B g x m v : ℝ)
    (hη : 0 ≤ η) (hε : 0 < ε)
    (hβ₁0 : 0 ≤ β₁) (hβ₁1 : β₁ ≤ 1)
    (hβ₂0 : 0 ≤ β₂) (hβ₂1 : β₂ ≤ 1) (hv : 0 ≤ v)
    (hm : |m| ≤ B) (hg : |g| ≤ B) :
    |AdamUpdate β₁ β₂ η ε g x m v - x| ≤ η * B / ε := by
  have hstep := adam_step_abs_le_eta β₁ β₂ η ε g x m v hη hε hβ₂0 hβ₂1 hv
  have hm' := adam_moment_step_bound β₁ g m B hβ₁0 hβ₁1 hm hg
  have hnum : η * |AdamM β₁ g m| ≤ η * B := mul_le_mul_of_nonneg_left hm' hη
  calc
    |AdamUpdate β₁ β₂ η ε g x m v - x| ≤ η * |AdamM β₁ g m| / ε := hstep
    _ ≤ η * B / ε := div_le_div_of_nonneg_right hnum (le_of_lt hε)

/-! ## 定理八：零梯度零动量时不动（一致性检查）
g = 0 且 m = 0 ⟹ m' = 0，故 x' = x（Adam 在零梯度处保持参数）。-/

theorem adam_zero_gradient_fixed (β₁ β₂ η ε x : ℝ) :
    AdamUpdate β₁ β₂ η ε 0 x 0 0 = x := by
  unfold AdamUpdate AdamM AdamV
  simp

/-! ## 定理九：二阶矩与步长的一致性（v' = 0 时分母退化为 ε）
g = 0 且 v = 0 ⟹ v' = 0，denominator = ε。-/

theorem adam_zero_gradient_denominator (β₂ ε : ℝ) :
    Real.sqrt (AdamV β₂ 0 0) + ε = ε := by
  unfold AdamV
  simp

/-! ## 注：与 Adam 原论文的关系与诚实边界
  · Kingma & Ba 的 Adam 在第二步矩 v' 上同样使用偏差修正 v̂ = v'/(1 - β₂ᵗ)；
    本文件只形式化了**一阶矩**的偏差修正（adam_bias_correction），
    二阶矩的非负性（adam_v_nonneg）与分母下界（adam_denominator_pos）；
  · 步长有界的统一形式（adam_step_bounded_learning）是自适应方法的
    「不放大步长」性质的精确陈述；
  · 完整收敛定理（O(1/√T) 遗憾界 / 非凸情形到 ε-驻点）需要随机梯度的
    条件期望与方差假设、凸性或 Polyak-Łojasiewicz 条件、以及 β₁,β₂ 的
    衰减调度 —— 属于后续工作，不在本文件的确定性标量证明范围内。-/

end Lattice
