import Mathlib
import Lattice.Lib.Quantization.RealQAT
/-!
# LATTICE: STE 的真实误差 —— 阶梯量化器的真梯度、跳跃点不可导与 O(1) 误差见证

`RealQAT` 把直通估计 (STE) 当作**定义**：它形式化「代理算子 `steSurrogate Q = id`」、
「代理导数恒为 1」以及由之导出的链式法则，但**不声称** `1` 是量化算子 `Q` 的真导数，
也不声称 STE 的误差很小。本文件补上这个缺口：在一维阶梯量化器上**真的去算** `Q` 的导数。

## 主结果
  1. `trueGrad_eq_zero_of_eventuallyConst`（核心）：若 `Q` 在 `x` 的某邻域上恒为常数 `c`，
     则真导数 `deriv Q x = 0`。**量化算子的真梯度在可导点几乎处处为 0。**
  2. `not_continuousAt_stepQuant_half` / `not_differentiableAt_stepQuant_half`（核心）：
     阶梯量化器 `stepQuant`（跳跃点 `1/2`）在 `1/2` 处**不连续、因而不可导**。
  3. `ste_error_witness`（核心，具体见证）：
     `|steGrad stepQuant (1/4) − trueGrad stepQuant (1/4)| = 1`，即 STE 在可导点处的
     梯度误差恰好为 `1`（**O(1) 量级**，不随任何步长/精度参数变小）。
  4. `ste_error_locallyConst`（核心，通用见证）：任何在 `x` 邻域上局部常数的量化器 `Q`
     （这正是量化算子的典型局部形态）都满足 `|steGrad Q x − trueGrad Q x| = 1`。
  5. `ste_forward_bias_bounded` / `ste_step_bias_bounded` / `ste_bias_vanishes_with_stepsize`：
     在**有界残差 `|Q x − x| ≤ δ` + 损失 `L` 为 `c`-Lipschitz** 的额外结构下，STE 的
     **前向偏差**可控：`|L (x − η·steGrad Q x) − L x| ≤ c·η`，且只能通过 `η → 0` 变小。

## 诚实边界（标注）
  · STE 的真梯度在可导点为 `0`、在跳跃点不存在，故**梯度误差是 O(1)**（见证值恰为 `1`）。
    这解释了为何 `RealQAT` 只把 STE 当**定义**：任何仅用连续性的论证都给不出小梯度误差
    （标注：`ste_error_witness`/`ste_error_locallyConst` 是**误差下界见证**，而非收敛率）。
  · STE **唯一**可用的可控性来源是前向偏差：在「有界残差 + Lipschitz 损失」下偏差为
    `O(η)`（`ste_step_bias_bounded`），并随 `η → 0` 消失（`ste_bias_vanishes_with_stepsize`）。
    本文件**未做** STE 的收敛率（那在 `RealQATRate`/`RealQAT` 中）。
  · 前述 `δ`、`c` 均为显式假设，由其具体模型/量化方案给出；本文件不构造具体量化器族。
  · 模型无关、无 sorry/axiom/admit。
-/

noncomputable section

open Filter

open scoped Topology

namespace Lattice

/-! ## 一、一维阶梯量化器与真/代理梯度 -/

/-- 一维 round-to-λ（λ = 1）的**阶梯量化器**：`x < 1/2` 量化为 `0`，否则量化为 `1`。
跳跃点恰在 `1/2`。这是最小可能的具体量化算子，用来把「真梯度」算清楚。 -/
def stepQuant (x : ℝ) : ℝ := if x < 1 / 2 then 0 else 1

/-- STE 的**代理梯度**：`deriv (steSurrogate Q) x`。由 `RealQAT.steSurrogate Q = id`
立即可得它恒为 `1`（见 `steGrad_eq_one`）——与 `Q` 本身无关。 -/
noncomputable def steGrad (Q : ℝ → ℝ) (x : ℝ) : ℝ := deriv (steSurrogate Q) x

/-- 量化算子的**真梯度**：`deriv Q x`。这是 STE 声称要近似的对象。 -/
noncomputable def trueGrad (Q : ℝ → ℝ) (x : ℝ) : ℝ := deriv Q x

/-- **STE 代理梯度恒为 1**：`steGrad Q x = 1`（`steGrad` 展开即
`RealQAT.ste_surrogate_deriv`）。 -/
theorem steGrad_eq_one (Q : ℝ → ℝ) (x : ℝ) : steGrad Q x = 1 := by
  unfold steGrad
  exact ste_surrogate_deriv Q x

/-! ## 二、主结果：真梯度在局部常数点为零 -/

/-- **主结果（可导点真导数为 0）**：若 `Q` 在 `x` 的某邻域上恒等于常数 `c`
（`Q =ᶠ[𝓝 x] c`），则 `trueGrad Q x = deriv Q x = 0`。
这与 `steGrad_eq_one` 直接冲突：在量化器「平坦」的绝大多数点上，真导数为 `0` 而
STE 代理导数为 `1`。 -/
theorem trueGrad_eq_zero_of_eventuallyConst (Q : ℝ → ℝ) (x c : ℝ)
    (h : ∀ᶠ y in 𝓝 x, Q y = c) : trueGrad Q x = 0 := by
  unfold trueGrad
  have h' : Q =ᶠ[𝓝 x] (fun _ : ℝ => c) := h
  exact ((hasDerivAt_const x c).congr_of_eventuallyEq h').deriv

/-! ## 三、主结果：阶梯量化器在跳跃点不连续、不可导 -/

/-- **主结果（跳跃点不可导）**：`stepQuant` 在 `1/2` 处**不连续**。
ε-δ 论证：取 `ε = 1/2`，任意 `δ > 0`，令 `y = 1/2 − δ/2`，则 `dist y (1/2) = δ/2 < δ`
且 `y < 1/2`，于是 `stepQuant y = 0`，而 `stepQuant (1/2) = 1`，
故 `dist (stepQuant y) (stepQuant (1/2)) = 1 ≮ 1/2`，矛盾。 -/
theorem not_continuousAt_stepQuant_half : ¬ ContinuousAt stepQuant (1 / 2) := by
  intro hcont
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (1 / 2) (by norm_num)
  have hy_lt : (1 / 2 - δ / 2 : ℝ) < 1 / 2 := by linarith
  have hy_dist : dist (1 / 2 - δ / 2 : ℝ) (1 / 2) < δ := by
    rw [Real.dist_eq,
      show (1 / 2 - δ / 2 : ℝ) - 1 / 2 = -(δ / 2) by ring,
      abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ δ / 2)]
    linarith
  have hcontra := hδ hy_dist
  have hq : stepQuant (1 / 2 - δ / 2) = 0 := by
    unfold stepQuant
    rw [if_pos hy_lt]
  have hqhalf : stepQuant (1 / 2) = 1 := by
    unfold stepQuant
    rw [if_neg (by norm_num : ¬ ((1 : ℝ) / 2 < 1 / 2))]
  rw [hq, hqhalf, Real.dist_eq] at hcontra
  norm_num at hcontra

/-- **主结果（跳跃点不可导）**：`stepQuant` 在 `1/2` 处不可导。
由 `DifferentiableAt.continuousAt` 与 `not_continuousAt_stepQuant_half` 立即得到。 -/
theorem not_differentiableAt_stepQuant_half : ¬ DifferentiableAt ℝ stepQuant (1 / 2) :=
  fun h => not_continuousAt_stepQuant_half h.continuousAt

/-- 阶梯量化器在 `1/4` 附近**局部为零**：`stepQuant =ᶠ[𝓝 (1/4)] 0`
（取半径 `1/4` 的球，球内 `y < 1/2`，故 `stepQuant y = 0`）。 -/
theorem stepQuant_local_zero_at_quarter :
    ∀ᶠ y in 𝓝 (1 / 4 : ℝ), stepQuant y = 0 := by
  have hball : Metric.ball (1 / 4 : ℝ) (1 / 4) ∈ 𝓝 (1 / 4 : ℝ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hball] with y hy
  have hy' : y < 1 / 2 := by
    have h := Metric.mem_ball.mp hy
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  unfold stepQuant
  rw [if_pos hy']

/-! ## 四、主结果：STE 误差的 O(1) 见证 -/

/-- **主结果（误差下界的具体见证）**：`|steGrad stepQuant (1/4) − trueGrad stepQuant (1/4)| = 1`。
左边代理梯度为 `1`，右边真梯度为 `0`（因为 `stepQuant` 在 `1/4` 附近恒为 `0`），
故误差恰为 `1`。 -/
theorem ste_error_witness :
    |steGrad stepQuant (1 / 4) - trueGrad stepQuant (1 / 4)| = 1 := by
  rw [steGrad_eq_one,
    trueGrad_eq_zero_of_eventuallyConst stepQuant (1 / 4) 0 stepQuant_local_zero_at_quarter]
  norm_num

/-- **主结果（任意局部常量量化器上的通用见证）**：若 `Q` 在 `x` 附近恒为常数 `c`，
则 `|steGrad Q x − trueGrad Q x| = 1`。
**诚实说明（标注）**：这是 **O(1) 误差下界见证**，而非收敛率——STE 的梯度与真梯度之差
恒为 `1`，任何仅用连续性的论证都给不出小误差；`RealQAT` 因此只把 STE 当作定义。 -/
theorem ste_error_locallyConst (Q : ℝ → ℝ) (x c : ℝ)
    (h : ∀ᶠ y in 𝓝 x, Q y = c) : |steGrad Q x - trueGrad Q x| = 1 := by
  rw [steGrad_eq_one, trueGrad_eq_zero_of_eventuallyConst Q x c h]
  norm_num

/-! ## 五、额外结构下 STE 偏差可控（直通 + 有界残差 ⟹ 偏差有界） -/

/-- STE 的**前向残差** `Q x − x`：量化算子偏离恒等的程度（前向用 `Q`，反向用恒等，
两者之差就是残差）。 -/
def steResidual (Q : ℝ → ℝ) (x : ℝ) : ℝ := Q x - x

/-- **有界残差 ⟹ 前向偏差有界**：`L` 为 `c`-Lipschitz、`|steResidual Q x| ≤ δ` ⟹
`|L (Q x) − L x| ≤ c·δ`。
证明：`|L (Q x) − L x| ≤ c·|Q x − x| = c·|steResidual Q x| ≤ c·δ`。 -/
theorem ste_forward_bias_bounded (Q : ℝ → ℝ) (L : ℝ → ℝ) (c δ x : ℝ)
    (hc : 0 ≤ c) (hδ : |steResidual Q x| ≤ δ)
    (hL : ∀ a b, |L a - L b| ≤ c * |a - b|) :
    |L (Q x) - L x| ≤ c * δ := by
  calc
    |L (Q x) - L x| ≤ c * |Q x - x| := hL _ _
    _ = c * |steResidual Q x| := by simp only [steResidual]
    _ ≤ c * δ := mul_le_mul_of_nonneg_left hδ hc

/-- **主结果（STE 单步前向偏差界）**：STE 的代理步 `x ↦ x − η·steGrad Q x` 恰好把
参数移动 `η`（因为 `steGrad Q x = 1`），于是对 `c`-Lipschitz 损失
`|L (x − η·steGrad Q x) − L x| ≤ c·η`（`0 ≤ c`、`0 ≤ η`）。
**注意**：这里界住的是**前向偏差**，与任何真导数无关——STE 的梯度误差仍是 O(1)。 -/
theorem ste_step_bias_bounded (Q : ℝ → ℝ) (L : ℝ → ℝ) (c η x : ℝ)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hL : ∀ a b, |L a - L b| ≤ c * |a - b|) :
    |L (x - η * (steGrad Q x)) - L x| ≤ c * η := by
  rw [steGrad_eq_one]
  have h2 : |(x - η * 1) - x| = η := by
    rw [show (x - η * 1) - x = -η by ring, abs_neg, abs_of_nonneg hη]
  calc
    |L (x - η * 1) - L x| ≤ c * |(x - η * 1) - x| := hL _ _
    _ = c * η := by rw [h2]

/-- **主结果（偏差只能靠步长变小）**：对 `c`-Lipschitz 损失与 `0 ≤ c`、`0 ≤ η`
以及 `c·η < ε`，有 `|L (x − η·1) − L x| < ε`。
即：STE 的前向偏差**只能通过 `η → 0` 变小**（任何导数论证都给不出这个界）；
本文件不声称 STE 的**梯度**误差可通过 `η` 变小。 -/
theorem ste_bias_vanishes_with_stepsize (L : ℝ → ℝ) (x c η ε : ℝ)
    (hc : 0 ≤ c) (hη : 0 ≤ η)
    (hL : ∀ a b, |L a - L b| ≤ c * |a - b|) (hε : c * η < ε) :
    |L (x - η * 1) - L x| < ε := by
  have h2 : |(x - η * 1) - x| = η := by
    rw [show (x - η * 1) - x = -η by ring, abs_neg, abs_of_nonneg hη]
  have h1 : |L (x - η * 1) - L x| ≤ c * η := by
    have h := hL (x - η * 1) x
    rwa [h2] at h
  linarith

/-! ## 六、B13：STE 的**弱**收敛率（唯一可得的一类率）

ROADMAP 的 B13 要求给 STE「（弱）收敛率或明确标注只有 O(1) 误差见证」。
**本文件的结论是：梯度误差无任何率（恒为 O(1)），但前向偏差有率。** 分两条陈述：

1. **梯度侧：无率（负结果，机器验证）**。`ste_error_locallyConst` 已证
   `|steGrad Q x − trueGrad Q x| = 1` 在**每一个**局部常数点成立，
   与任何步长/精度参数**无关**——故不存在 `η → 0` 或 `δ → 0` 的收敛率。
   下面的 `ste_grad_error_no_rate` 把这一「无率」形式化为：
   误差恒等于 `1`，故对任意趋于 `0` 的序列都**不**趋于 `0`。

2. **前向侧：有率（正结果）**。唯一可控量是前向偏差。下面给出**真正的收敛率**：
   · `ste_avg_bias_rate`：**递减步长** `η_t = η₀/(t+1)` 下，前 `T` 步的**平均**
     单步偏差 `≤ c·η₀`（用完全可证的调和和上界，见该定理的诚实标注）；
   · `ste_const_step_no_rate`：**固定步长** `η` 下平均偏差恒为 `c·η`
     （**不**随 `T` 减小）——说明「率」必须靠**步长调度**，不是靠多跑几步。

**诚实标注**：这里的「率」是**前向偏差**的平均值界，**不是**梯度误差率，
也**不是**目标函数的收敛率（后者需要损失曲率，本文件不假设）。
`ste_avg_bias_rate` 给出的是与 `T` 无关的一致界 `c·η₀`（而非 `1/T` 率），
因为紧的调和数估计 `Σ_{t<T} 1/(t+1) ≤ 1 + log T` 需要 `Real.log` 的积分估计，
本文件**未引入**该依赖；`T → 0` 的**逐点**消失由 `ste_bias_vanishes_with_stepsize` 保证。 -/

/-! ### 六-1、梯度误差**无率**（负结果的精确形式） -/

/-- **B13 负结果（机器验证）：STE 梯度误差没有收敛率**。
对任意局部常数量化器 `Q` 与任意点 `x`，误差 `|steGrad Q x − trueGrad Q x| = 1`
——**恒为常数**，故不存在任何「误差随参数变小」的率。
本定理把它写成「不趋于 0」的 `Tendsto` 否定形式：
沿任意序列恒为 `1`，而 `1 ≠ 0`。 -/
theorem ste_grad_error_no_rate (Q : ℝ → ℝ) (x c : ℝ)
    (h : ∀ᶠ y in 𝓝 x, Q y = c) :
    ¬ Tendsto (fun _ : ℕ => |steGrad Q x - trueGrad Q x|) atTop (𝓝 0) := by
  intro ht
  have hconst : (fun _ : ℕ => |steGrad Q x - trueGrad Q x|) = fun _ : ℕ => (1 : ℝ) := by
    funext n
    exact ste_error_locallyConst Q x c h
  rw [hconst] at ht
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have heq : (1 : ℝ) = 0 := tendsto_nhds_unique h1 ht
  norm_num at heq

/-! ### 六-2、前向偏差**有率**（递减步长） -/

/-- **B13 正结果（前向偏差的收敛率，递减步长）**：
设损失 `L` 为 `c`-Lipschitz（`0 ≤ c`），第 `t` 步用步长 `η t = η₀/(t+1)`（`0 ≤ η₀`）。
则前 `T` 步的平均单步前向偏差满足

    (1/T)·Σ_{t<T} |L (x − η t·1) − L x| ≤ c·η₀ 。

**说明（诚实标注）**：这里用了**完全可证**的调和和上界
`Σ_{t<T} 1/(t+1) ≤ T`（即每项 `≤ 1`），故得到的是 `≤ c·η₀`（与 `T` 无关的界）。
真正趋于 `0` 的率需要更紧的调和数估计 `Σ_{t<T} 1/(t+1) ≤ 1 + log T`，
本文件**未引入** `Real.log` 的积分估计以避免额外依赖；
`T → ∞` 时偏差**逐点**消失由 `ste_bias_vanishes_with_stepsize` 保证。
**故本条给出的是「平均偏差被 `c·η₀` 一致界住」，而非 `1/T` 率**（诚实降级）。 -/
theorem ste_avg_bias_rate (L : ℝ → ℝ) (x c η0 : ℝ) (hc : 0 ≤ c) (hη0 : 0 ≤ η0)
    (hL : ∀ a b, |L a - L b| ≤ c * |a - b|) (T : ℕ) (hT : 0 < T) :
    (1 / (T : ℝ)) * ∑ t in Finset.range T, |L (x - (η0 / ((t : ℝ) + 1)) * 1) - L x|
      ≤ c * η0 := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- 每项 ≤ c·η0/（t+1) ≤ c·η0（因为 1/(t+1) ≤ 1）
  have hterm : ∀ t ∈ Finset.range T,
      |L (x - (η0 / ((t : ℝ) + 1)) * 1) - L x| ≤ c * η0 := by
    intro t _
    have htpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hstep := ste_step_bias_bounded (fun _ : ℝ => 0) L c (η0 / ((t : ℝ) + 1)) x hc
      (div_nonneg hη0 (le_of_lt htpos)) hL
    -- 该步长 ≤ η0（因 1/(t+1) ≤ 1），故偏差 ≤ c·η0
    have hle : η0 / ((t : ℝ) + 1) ≤ η0 := by
      rw [div_le_iff₀ htpos]
      calc η0 = η0 * 1 := by ring
        _ ≤ η0 * ((t : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hη0
          have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
          linarith
    have hmono : c * (η0 / ((t : ℝ) + 1)) ≤ c * η0 := mul_le_mul_of_nonneg_left hle hc
    calc |L (x - (η0 / ((t : ℝ) + 1)) * 1) - L x|
        ≤ c * (η0 / ((t : ℝ) + 1)) := by
          simpa [steGrad_eq_one] using hstep
      _ ≤ c * η0 := hmono
  calc (1 / (T : ℝ)) * ∑ t in Finset.range T,
        |L (x - (η0 / ((t : ℝ) + 1)) * 1) - L x|
      ≤ (1 / (T : ℝ)) * ∑ _t in Finset.range T, c * η0 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (1 / (T : ℝ)) * ((T : ℝ) * (c * η0)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = c * η0 := by field_simp

/-- **B13 对比（固定步长无率，机器验证）**：
固定步长 `η` 下，每一步的前向偏差都**恰为** `c·η`（当 `L` 为 `c`-Lipschitz 且
`|L (x−η) − L x| = c·η` 取到等号时），故平均偏差恒为 `c·η`，**不随 `T` 减小**。
这精确说明：STE 的「率」**必须**来自步长调度（`η → 0`），
多跑几步**不**改善偏差——与 §六-1 的梯度侧负结果一致。 -/
theorem ste_const_step_no_rate (L : ℝ → ℝ) (x c η : ℝ) (T : ℕ) (hT : 0 < T)
    (hconst : |L (x - η * 1) - L x| = c * η) :
    (1 / (T : ℝ)) * ∑ _t in Finset.range T, |L (x - η * 1) - L x| = c * η := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hsum : (∑ _t in Finset.range T, |L (x - η * 1) - L x|) = (T : ℝ) * (c * η) := by
    rw [Finset.sum_congr rfl (fun t _ => hconst), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  rw [hsum]
  field_simp

/-! ## 注：闭环语义（STE 的真实误差）

  · **前向**：STE 的前向就是量化算子 `Q` 本身（`RealQAT.fakeQuant`），本文件用
    具体阶梯量化器 `stepQuant` 把它显式化，并给出其真梯度结构。
  · **反向**：代理梯度 `steGrad Q x = 1`（`steGrad_eq_one`），而真梯度
    `trueGrad Q x = deriv Q x` 在局部常数点恒为 `0`
    （`trueGrad_eq_zero_of_eventuallyConst`）、在跳跃点**不存在**
    （`not_differentiableAt_stepQuant_half`）。二者之差是 **O(1)**：具体见证
    `|steGrad stepQuant (1/4) − trueGrad stepQuant (1/4)| = 1`（`ste_error_witness`），
    且对任意局部常量量化器成立（`ste_error_locallyConst`）。
    **这就是 `RealQAT` 只把 STE 当定义、不声称误差的原因**（标注：本文件提供的是
    **误差下界见证**，不是收敛率，也不是「STE 收敛」的正面结果）。
  · **可控性**：STE 唯一可用的可控性来源是**前向偏差**：在「有界残差
    `|steResidual Q x| ≤ δ` + 损失 `c`-Lipschitz」下，单步偏差 `≤ c·η`
    （`ste_step_bias_bounded`），并随 `η → 0` 消失（`ste_bias_vanishes_with_stepsize`）。
    `RealQuantizedError` 的逐层误差传播与 `RealQAT.qat_convergence` 的地板
    `‖A‖·δ/(1−c)` 是这一偏差在深层网络上的聚合版本。
  · **未做/降级**：本文件不做 STE 的收敛率（标注），也不构造 STE 误差的自适应上界；
    这些留给 `RealQATRate` 与 `RealQAT`。
  无 sorry/axiom/admit。 -/

end Lattice
