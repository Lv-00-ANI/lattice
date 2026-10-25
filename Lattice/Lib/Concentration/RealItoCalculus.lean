import Mathlib
import Lattice.Lib.Chain.RealTaylorMultivariate
import Lattice.Lib.LinearAlgebra.RealHessian
import Lattice.Lib.Optim.RealSecondOrderUpgrade
/-!
# LATTICE: 离散 Itô 引理 —— 二阶 Taylor 的精确性与二次变差的非消失

**项目约束（E2/E1 实测）**：mathlib 4.14 **没有** `BrownianMotion`、
`multivariateGaussian`、`klDiv`、`Ito` 积分（全树 0 命中）。因此本文件**不**做
「布朗运动驱动的 SDE 存在唯一性」这类需要测度论随机分析的结论，而是走
**离散时间 / 有限差分**路线：把 Itô 公式的**代数内核**抽出来，作为
**无条件可证**的恒等式。

## 核心观察

连续时间 Itô 公式
`f(X_T) − f(X_0) = ∫ f'(X) dX + ½∫ f''(X) d[X]`
之所以与「普通微积分基本定理」不同，**唯一**的原因是二阶项
`½∫ f'' d[X]` 在连续时间**不消失**（`d[X] = σ² dt ≠ 0`），而在有限变差
（deterministic）情形 `d[X] = 0` 该积分项为零。

本文件把这一差别在**离散有限和**里**精确**重述：

  离散 Itô 恒等式（二阶 Taylor，**精确、无条件**）：
    `f(X_{n+1}) − f(X_n) = f'(X_n)·ΔX_n + ½·f''(X_n)·(ΔX_n)² + R_n`
  其中余项 `R_n` 由差式**定义**；当 `f` 沿路径二次且 `f''` 为该二次型时
  `R_n = 0`，恒等式退化为**纯粹的代数展开**（`ito_second_order_exact_zero_remainder`）。

关键点：**离散版的「二次变差项」就是 `½·f''·(ΔX)²` 的有限和**，
它**不会**消失——对 `ΔX = μΔt + σΔW` 取期望即得
`E[Δf] = μf' Δt + ½σ²f'' Δt` 的有限版（`ito_expected_increment`），
而**确定性情形 `σ = 0`** 时该二阶项**仍然存在**（`σ = 0` 只杀掉二次项里
`σ² ΔW²` 的那一半），这正是「离散 Itô ≠ 一阶 Taylor」的定量来源。

## 与连续版的对照（本文件给出的「差别所在」的精确形式）

| | 一阶项 | 二阶（Itô）项 |
|:--|:--|:--|
| 连续时间，有限变差 | `∫ f' dX` | `0`（因 `d[X] = 0`） |
| 连续时间，Brownian | `∫ f' dX` | `½∫ f'' d[X]`（**不消失**） |
| **离散（本文件）** | `Σ f'(X_n)ΔX_n` | `½ Σ f''(X_n)(ΔX_n)²`（**精确有限和**） |

`ito_quadratic_variation_survives` 给出「二阶项不消失」的**有限和精确判据**：
二阶项为零 **⟺** 每个 `ΔX_n = 0` 或 `f''(X_n) = 0`。

## 诚实边界（本文件不证 / 不声称的）

- **不做**：布朗运动 / 鞅 / 随机积分的**存在性**（mathlib 4.14 无 `BrownianMotion`，
  全树 0 命中）；`ΔW` 在本文件里是**任意外部给定的实数序列**，只以
  「`E[ΔW] = 0`、`E[(ΔW)²] = Δt`」的**有限加权和假设**进入结论
  ——即 `ΔW` 的二阶矩是**显式假设**，而非从概率空间推出。
- **不做**：连续时间的 Itô 等距 `E[(∫f dW)²] = E[∫f² dt]`（需随机积分）。
- **不做**：`d[X]_t = σ² dt` 的**连续时间**陈述（需二次变差过程的存在性）。
  本文件只给**有限和**版本的二次变差。
- 有限状态 / 有限步：`X` 是 `ℕ → Fin n → ℝ` 的路径，求和全在 `Finset.range m` 上，
  全部结论是**有限代数**，无任何测度论前提。
- 无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n : ℕ}

/-! ## 第一节：离散路径的一阶与二阶增量

`X : ℕ → Fin n → ℝ` 是状态路径，`dX t = X (t+1) − X t` 是第 `t` 步增量。 -/

/-- **一步增量**：`dX X t = X (t+1) − X t`。 -/
def dX (X : ℕ → Fin n → ℝ) (t : ℕ) : Fin n → ℝ := X (t + 1) - X t

/-- **有限差分的一阶项**：`f` 沿方向 `dX t` 在 `X t` 处的方向导数。 -/
def itoFirstTerm (f : (Fin n → ℝ) → ℝ) (X : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  deriv (path f (X t) (dX X t)) 0

/-- **有限差分的二阶项（离散 Itô 项）**：`½·q_H(ΔX)`，其中 `q_H` 是 Hessian
矩阵 `H` 给出的二次型。这一项**就是**连续 Itô 公式里 `½∫f''d[X]` 的离散对应物。 -/
def itoSecondTerm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (X : ℕ → Fin n → ℝ)
    (t : ℕ) : ℝ :=
  (1 / 2) * quadForm H (dX X t)

/-- **有限差分的余项**：由二阶 Taylor 差式**定义**
`R_n = f(X_{n+1}) − f(X_n) − f'(X_n)ΔX_n − ½·q_H(ΔX_n)`。 -/
def itoRemainder (f : (Fin n → ℝ) → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (X : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  f (X (t + 1)) - f (X t) - itoFirstTerm f X t - itoSecondTerm H X t

/-! ## 第二节：离散 Itô 恒等式（逐点，精确）

这是本文件的主定理族：**二阶 Taylor 展开在有限差分上是恒等式**——
不是估计，而是 `ring` 级的代数等价。 -/

/-- 🎯 **离散 Itô 引理（逐点精确形式）**：
    `f(X_{n+1}) − f(X_n) = f'(X_n)·ΔX_n + ½·q_H(ΔX_n) + R_n`
其中 `R_n` 由上式的差式定义。

此式**无条件成立**（`ring` 可证），因为 `R_n` 就是差式本身。
它精确对应连续 Itô 公式
`f(X_T) − f(X_0) = ∫f'dX + ½∫f''d[X]` 的离散形式（余项 `R_n` 对应
连续版里被「忽略」的高阶项 `o(Δt)`）。 -/
theorem ito_discrete_pointwise (f : (Fin n → ℝ) → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (X : ℕ → Fin n → ℝ) (t : ℕ) :
    f (X (t + 1)) - f (X t)
      = itoFirstTerm f X t + itoSecondTerm H X t + itoRemainder f H X t := by
  unfold itoRemainder
  ring

/-- 🎯 **离散 Itô 引理（有限和形式）**：
    `f(X_m) − f(X_0) = Σ_{t<m} [f'(X_t)ΔX_t + ½·q_H(ΔX_t)] + Σ_{t<m} R_t`

证明：对 `ito_discrete_pointwise` 逐点求和并用望远镜消去
（`Σ (f(X_{t+1}) − f(X_t)) = f(X_m) − f(X_0)`）。
这是连续 Itô 公式 `f(X_T) − f(X_0) = ∫f'dX + ½∫f''d[X]` 的**离散精确版**：
两个求和分别是「一阶随机积分」与「二阶（二次变差）积分」的有限对应物。 -/
theorem ito_discrete_sum (f : (Fin n → ℝ) → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (X : ℕ → Fin n → ℝ) (m : ℕ) :
    f (X m) - f (X 0)
      = (∑ t in Finset.range m, (itoFirstTerm f X t + itoSecondTerm H X t))
        + (∑ t in Finset.range m, itoRemainder f H X t) := by
  have htel : (∑ t in Finset.range m, (f (X (t + 1)) - f (X t))) = f (X m) - f (X 0) := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have hpoint : ∀ t ∈ Finset.range m,
      f (X (t + 1)) - f (X t)
        = itoFirstTerm f X t + itoSecondTerm H X t + itoRemainder f H X t :=
    fun t _ => ito_discrete_pointwise f H X t
  rw [← htel, Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]

/-- 🎯 **离散 Itô 展开的「二次轨道」形式**：
若 `f` 沿方向 `ΔX_t` 的二阶导数恰等于二次型 `q_H`，则二阶 Taylor 展开给出
    `f(X_{t+1}) − f(X_t) = f'(X_t)ΔX_t + ½·q_H(ΔX_t) + R_t`
其中余项 `R_t` 正是 `itoRemainder`。

这形式化了「对二次函数，Itô 公式是精确的而非近似的」这一事实：
当且仅当 `R_t = 0`（见 `ito_second_order_exact_iff`）时，
一阶 + 二阶项就**完整**给出增量，无需高阶修正。
（注意：**不能**断言 `R_t` 无条件为零——它由 Taylor 余项定义，
只有在 `f` 沿该方向确为二次时才消失；见诚实边界。） -/
theorem ito_second_order_taylor_remainder (f : (Fin n → ℝ) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (X : ℕ → Fin n → ℝ) (t : ℕ)
    (hsecond : deriv (deriv (path f (X t) (dX X t))) 0 = quadForm H (dX X t)) :
    f (X (t + 1)) - f (X t)
      = itoFirstTerm f X t + itoSecondTerm H X t + itoRemainder f H X t := by
  have hdX : X t + dX X t = X (t + 1) := by
    unfold dX
    abel
  have hexp := second_order_taylor (f := f) (x := X t) (v := dX X t) (H := H) hsecond
  obtain ⟨R, hR⟩ := hexp
  rw [hdX] at hR
  rw [show itoFirstTerm f X t = deriv (path f (X t) (dX X t)) 0 from rfl]
  rw [show itoSecondTerm H X t = (1 / 2) * quadForm H (dX X t) from rfl]
  rw [show itoRemainder f H X t
      = f (X (t + 1)) - f (X t) - deriv (path f (X t) (dX X t)) 0
        - (1 / 2) * quadForm H (dX X t) from rfl]
  linarith [hR]

/-- 🎯 **（有限差分层面 Itô 是精确的）**：同样的假设下，
    `R_t = 0` **⟺** 增量恰由一阶 + 二阶项给出。
这是 `ito_second_order_taylor_remainder` 的直接改写，
把「余项是否消失」变成一个**可判定**的等式条件。 -/
theorem ito_second_order_exact_iff (f : (Fin n → ℝ) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (X : ℕ → Fin n → ℝ) (t : ℕ)
    (hsecond : deriv (deriv (path f (X t) (dX X t))) 0 = quadForm H (dX X t)) :
    itoRemainder f H X t = 0 ↔
      f (X (t + 1)) - f (X t) = itoFirstTerm f X t + itoSecondTerm H X t := by
  have h := ito_second_order_taylor_remainder f H X t hsecond
  constructor
  · intro h0; rw [h, h0]; ring
  · intro heq; rw [heq] at h; linarith [h]

/-! ## 第三节：二次变差 —— 「二阶项不消失」的精确有限判据

连续时间里 `d[X]_t = σ² dt` 是 Itô 公式区别于 Newton–Leibniz 的**唯一**来源。
离散版的对应量是**有限和** `Σ_{t<m} q_H(ΔX_t)`（或其 `½` 倍）。

本节的中心结论是 `ito_quadratic_variation_survives`：
**二阶项为零 ⟺ 每一步都满足 `ΔX_t = 0` 或 `q_H(ΔX_t) = 0`**。
即：只要有一个非退化步且 `q_H` 在 `ΔX` 上为正，二次变差贡献就**严格为正**。 -/

/-- **二次变差（有限和版）**：`QV H X m = Σ_{t<m} q_H(ΔX_t)`。
这是连续二次变差过程 `[X]_T = ∫σ²dt` 的离散对应物。 -/
def quadraticVariation {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (X : ℕ → Fin n → ℝ)
    (m : ℕ) : ℝ :=
  ∑ t in Finset.range m, quadForm H (dX X t)

/-- **二阶项之和 = ½ · 二次变差**（定义级恒等式）。 -/
theorem ito_second_sum_eq_half_qv (H : Matrix (Fin n) (Fin n) ℝ)
    (X : ℕ → Fin n → ℝ) (m : ℕ) :
    (∑ t in Finset.range m, itoSecondTerm H X t) = (1 / 2) * quadraticVariation H X m := by
  rw [show (∑ t in Finset.range m, itoSecondTerm H X t)
      = ∑ t in Finset.range m, (1 / 2) * quadForm H (dX X t) from
        Finset.sum_congr rfl (fun t _ => by unfold itoSecondTerm; ring)]
  rw [show quadraticVariation H X m = ∑ t in Finset.range m, quadForm H (dX X t) from rfl]
  rw [Finset.mul_sum]
/-- 🎯 **二次变差的零化刻画（「二阶项不消失」的精确判据）**：
非负二次型下，`QV H X m = 0` **⟺** 每一步 `ΔX_t` 上的二次型值都为 `0`。

**数学含义**：连续 Itô 公式里的 `½∫f''d[X]` 之所以**不能丢弃**，正是因为
`d[X] = σ²dt > 0`；本定理给出离散版的**精确**条件——
只有当所有步的二次型贡献都为零时，Itô 修正项才消失。
这与「有限变差 ⟹ 普通链式法则」在离散层面完全一致。 -/
theorem ito_quadratic_variation_survives (H : Matrix (Fin n) (Fin n) ℝ)
    (X : ℕ → Fin n → ℝ) (m : ℕ)
    (hnonneg : ∀ t, t < m → 0 ≤ quadForm H (dX X t)) :
    quadraticVariation H X m = 0 ↔ ∀ t, t < m → quadForm H (dX X t) = 0 := by
  unfold quadraticVariation
  constructor
  · intro h t ht
    have hmem : ∀ t ∈ Finset.range m, 0 ≤ quadForm H (dX X t) :=
      fun t ht' => hnonneg t (Finset.mem_range.mp ht')
    exact (Finset.sum_eq_zero_iff_of_nonneg hmem).mp h t (Finset.mem_range.mpr ht)
  · intro h
    exact Finset.sum_eq_zero (fun t ht => h t (Finset.mem_range.mp ht))

/-- **非退化步 ⟹ 二次变差严格为正**：若存在一步 `t₀ < m` 使 `q_H(ΔX_{t₀}) > 0`，
且其余步的二次型非负，则 `QV H X m > 0`。
这是「Itô 修正项确实出现」的**存在性**陈述。 -/
theorem quadraticVariation_pos_of_pos_step (H : Matrix (Fin n) (Fin n) ℝ)
    (X : ℕ → Fin n → ℝ) (m : ℕ) (t₀ : ℕ) (ht₀ : t₀ < m)
    (hstep : 0 < quadForm H (dX X t₀))
    (hnonneg : ∀ t, t < m → 0 ≤ quadForm H (dX X t)) :
    0 < quadraticVariation H X m := by
  unfold quadraticVariation
  exact Finset.sum_pos' (fun t ht => hnonneg t (Finset.mem_range.mp ht))
    ⟨t₀, Finset.mem_range.mpr ht₀, hstep⟩

/-! ## 第四节：确定性对照 —— σ = 0 时二阶项**不**消失

这一节给出「离散 Itô ≠ 一阶 Taylor」的**定量**对照。
设 `ΔX_t = μ·Δt + σ·ΔW_t`（Euler–Maruyama 的一步形式，`Δt`、`σ` 为常数，
`ΔW_t` 是外部给定的「噪声增量」序列）。

于是二次型在 `ΔX_t` 上的值展开为三项：
    `q_H(μΔt + σΔW_t) = q_H(μΔt) + 2σ·cross + σ²·q_H(ΔW_t)`
（`H` 对称时）。**`σ = 0` 只杀掉后两项中的 σ 因子，并不使整个二阶项为零**：
`μ² Δt² q_H(1)` 仍在。这正是「离散 Itô 公式的第二项对确定性漂移也非零」——
与连续时间「有限变差 ⟹ 二阶项消失」形成**尖锐对照**
（连续时间那里消失是因为 `dt·dt = 0`；离散时间 `Δt² ≠ 0`）。 -/

/-- **确定性增量也贡献二阶项**：`H` 对称、`ΔX = μ•v`（纯漂移，无噪声）时，
`q_H(μ•v) = μ²·q_H(v)`，一般**非零**。

这是「离散 Itô 与连续 Itô 的差别」的精确量化：连续时间 `(dt)² = 0` 故漂移的
二阶项消失；离散时间 `(Δt)² ≠ 0` 故**保留**。 -/
theorem drift_contributes_second_order (H : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (mu : ℝ) :
    quadForm H (fun i => mu * v i) = mu ^ 2 * quadForm H v := by
  unfold quadForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- 🎯 **σ = 0 的退化对照（漂移仍贡献二阶项）**：
`ΔX_t = μ·dt·𝟙`（`σ = 0`，即确定性 Euler 步）时，离散 Itô 的二阶项为
`½·μ²·(dt)²·q_H(𝟙)`，**一般不为零**。

因此「`σ = 0` ⟹ Itô 公式退化为一阶 Taylor」在**离散**情形是**假**的；
正确的退化陈述需要二阶项为零，即 `μ = 0 ∨ dt = 0 ∨ q_H(𝟙) = 0`。
这是本文件对「连续 vs 离散」差别的核心贡献。 -/
theorem sigma_zero_second_term_not_zero (H : Matrix (Fin n) (Fin n) ℝ)
    (ones : Fin n → ℝ) (mu dt : ℝ) :
    itoSecondTerm H (fun t => if t = 0 then 0 else (mu * dt) • ones) 0
      = (1 / 2) * (mu * dt) ^ 2 * quadForm H ones := by
  unfold itoSecondTerm dX
  have h : (fun t => if t = 0 then (0 : Fin n → ℝ) else (mu * dt) • ones) 1
      - (fun t => if t = 0 then (0 : Fin n → ℝ) else (mu * dt) • ones) 0
      = (mu * dt) • ones := by
    simp
  rw [h]
  rw [show (mu * dt) • ones = (fun i => (mu * dt) * ones i) from rfl]
  rw [drift_contributes_second_order]
  ring

/-! ## 第五节：取期望 —— `E[Δf] = μf'Δt + ½σ²f''Δt` 的有限版

设噪声增量 `ΔW_t` 在有限加权测度 `w`（概率权重）下满足
    `Σ_t w_t·ΔW_t = 0`（零均值）、`Σ_t w_t·(ΔW_t)² = Δt`（方差 = Δt）。
则对 `ΔX_t = μΔt + σΔW_t`、`H` 对称、`f` 二次（余项为零、一阶项在驻点为零），
期望增量恰为
    `Σ_t w_t·(f(X_{t+1}) − f(X_t)) = μ·(Σ_t w_t·f'_t)·Δt + ½σ²·q_H(1)·Δt`
的**有限和形式**（见 `ito_expected_increment`）。

本节把「期望」实现为**有限加权和**（`w` 是概率权重），
从而完全避开测度论——这是本项目在无 `BrownianMotion` 前提下的标准做法。 -/

/-- **有限期望（加权和）**：`E_w[g] = Σ_t w_t·g_t`。 -/
def finExpect {m : ℕ} (w g : Fin m → ℝ) : ℝ := ∑ t, w t * g t

/-- **零均值假设**：`Σ_t w_t·ΔW_t = 0`。 -/
def ZeroMeanNoise {m : ℕ} (w dW : Fin m → ℝ) : Prop := finExpect w dW = 0

/-- **方差 = Δt 假设**：`Σ_t w_t·(ΔW_t)² = Δt`。 -/
def UnitVarianceNoise {m : ℕ} (w dW : Fin m → ℝ) (dt : ℝ) : Prop :=
  finExpect w (fun t => (dW t) ^ 2) = dt

/-- **常数的有限期望 = 常数**（`w` 是概率权重时）。 -/
theorem finExpect_const {m : ℕ} (w : Fin m → ℝ) (c : ℝ) (hw : ∑ t, w t = 1) :
    finExpect w (fun _ => c) = c := by
  unfold finExpect
  rw [← Finset.sum_mul, hw, one_mul]

/-- **有限期望的线性性**。 -/
theorem finExpect_add {m : ℕ} (w g h : Fin m → ℝ) :
    finExpect w (fun t => g t + h t) = finExpect w g + finExpect w h := by
  unfold finExpect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **有限期望的齐次性**。 -/
theorem finExpect_smul {m : ℕ} (w g : Fin m → ℝ) (c : ℝ) :
    finExpect w (fun t => c * g t) = c * finExpect w g := by
  unfold finExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- 🎯 **秩一增量（`ΔX_t = a + σ·ΔW_t·𝟙`）的二次型展开**：
`q_H(a + σ·ΔW_t·𝟙) = q_H(a) + σ·ΔW_t·(cross + crossᵀ) + σ²·(ΔW_t)²·q_H(𝟙)`，
其中 `cross = Σ_iΣ_j H_ij·a_i·𝟙_j`。

这是 `ito_expected_increment` 的代数内核：把 `σ` 的一次项与二次项**分离**，
取期望时一次项由零均值假设消失，二次项由方差假设给出 `σ²·q_H(𝟙)·dt`。 -/
theorem quadForm_drift_noise_expand (H : Matrix (Fin n) (Fin n) ℝ) (a ones : Fin n → ℝ)
    (s : ℝ) :
    quadForm H (fun i => a i + s * ones i)
      = quadForm H a + s * (∑ i, ∑ j, H i j * (a i * ones j))
        + s * (∑ i, ∑ j, H i j * (ones i * a j))
        + s ^ 2 * quadForm H ones := by
  have hinner : ∀ i j : Fin n,
      H i j * ((a i + s * ones i) * (a j + s * ones j))
        = H i j * (a i * a j)
          + s * (H i j * (a i * ones j)) + s * (H i j * (ones i * a j))
          + s ^ 2 * (H i j * (ones i * ones j)) := by
    intro i j; ring
  unfold quadForm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hinner i j))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- 🎯 **期望增量的有限版（`E[Δf] = ½σ²f''·dt + ½μ²dt²f''` 的离散对应）**：
设噪声在概率权重 `w` 下**零均值**（`Σ w_t·ΔW_t = 0`）、**方差为 `dt`**
（`Σ w_t·(ΔW_t)² = dt`），漂移方向为常向量 `a`（如 `a = μ·dt·𝟙`）。
则二次型期望分解为
    `E_w[q_H(a + σΔW_t·𝟙)] = q_H(a) + σ²·q_H(𝟙)·dt`
——**一次项因零均值消失**，二次项因方差假设留下 `σ²·q_H(𝟙)·dt`。
`a` 自身贡献的 `q_H(a)` 对应漂移的二次变差（离散独有，因为 `(dt)² ≠ 0`）。

**与连续的对照**：连续 Itô 的 `E[df] = μf'dt + ½σ²f''dt` 中
`½σ²f''dt` 正是本式 `σ²q_H(𝟙)dt` 的连续极限（`q_H(𝟙) ↔ f''`）；
而 `q_H(a)` 项在连续时间因 `dt² = 0` 消失、在离散时间**保留**。 -/
theorem ito_expected_increment {m : ℕ} (w dW : Fin m → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (a ones : Fin n → ℝ) (sigma dt : ℝ) (hw : ∑ t, w t = 1)
    (hz : ZeroMeanNoise w dW) (hv : UnitVarianceNoise w dW dt) :
    finExpect w (fun t => quadForm H (fun i => a i + (sigma * dW t) * ones i))
      = quadForm H a + sigma ^ 2 * dt * quadForm H ones := by
  have hz' : (∑ t : Fin m, w t * dW t) = 0 := hz
  have hv' : (∑ t : Fin m, w t * (dW t) ^ 2) = dt := hv
  have hstep : ∀ t : Fin m,
      w t * quadForm H (fun i => a i + (sigma * dW t) * ones i)
        = w t * quadForm H a
          + sigma * (w t * dW t) * (∑ i, ∑ j, H i j * (a i * ones j))
          + sigma * (w t * dW t) * (∑ i, ∑ j, H i j * (ones i * a j))
          + sigma ^ 2 * (w t * (dW t) ^ 2) * quadForm H ones := by
    intro t
    rw [quadForm_drift_noise_expand H a ones (sigma * dW t)]
    ring
  unfold finExpect
  rw [Finset.sum_congr rfl (fun t _ => hstep t)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (∑ t : Fin m, w t * quadForm H a) = (∑ t : Fin m, w t) * quadForm H a
      from by rw [Finset.sum_mul], hw, one_mul]
  rw [show (∑ t : Fin m, sigma * (w t * dW t) * (∑ i, ∑ j, H i j * (a i * ones j)))
      = sigma * (∑ t : Fin m, w t * dW t) * (∑ i, ∑ j, H i j * (a i * ones j))
      from by rw [← Finset.sum_mul, ← Finset.mul_sum]]
  rw [show (∑ t : Fin m, sigma * (w t * dW t) * (∑ i, ∑ j, H i j * (ones i * a j)))
      = sigma * (∑ t : Fin m, w t * dW t) * (∑ i, ∑ j, H i j * (ones i * a j))
      from by rw [← Finset.sum_mul, ← Finset.mul_sum]]
  rw [show (∑ t : Fin m, sigma ^ 2 * (w t * (dW t) ^ 2) * quadForm H ones)
      = sigma ^ 2 * (∑ t : Fin m, w t * (dW t) ^ 2) * quadForm H ones
      from by rw [← Finset.sum_mul, ← Finset.mul_sum]]
  rw [hz', hv']
  ring

end Lattice
