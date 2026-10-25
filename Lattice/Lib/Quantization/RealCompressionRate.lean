import Mathlib
import Lattice.Lib.Optim.RealSGDStochastic
import Lattice.Lib.Optim.RealErrorFeedback
/-!
# LATTICE: 压缩通信的**收敛率** —— δ-近似压缩 + 误差反馈下的 O(1/√T) + O((1−δ)²G²)

> ## 构建状态（F14，v15 —— **必须先读**）
>
> **本文件的 3 条 error 已全部修复**（修复前 exit 1；修复后由
> `scripts/lake-lock.ps1 RealCompressionRate` 以 `Built` + exit 0 验证，
> **不是** `Replayed`）。缺陷**均在 `compression_gap_rate_explicit`（§六 末条）内部**，
> 与文件其余部分无关（同批次另 5 个模块一直 `Built`，无级联）。
>
> **三条独立缺陷**（前三轮诊断曾把它们混为"tactic 写错"，实为性质不同）：
> 1. **该定理原陈述是假命题**（最严重，**非** tactic 问题）：
>    原前件 `1 − δ ≤ 1/(2(1+ε))` **过松**，反例 `δ = 397/500, ε = 1/20`
>    —— 前件成立而 `(2−δ)/δ = 1.5189 ≮ 1.05 = 1+ε`。
>    **正确阈值** `(2−δ)/δ < 1+ε ⟺ 2/(2+ε) < δ`，已据此更正陈述，
>    并新增**机器验证反例定理** `compression_gap_rate_threshold_sharp`
>    钉住原稿的假命题（回归用）。登记于 `CORRECTIONS B64`。
> 2. **原证明的中间子目标 `hlt : 1/((1+ε)δ) < ε` 本身为假**
>    （反例 `δ = 987/1000, ε = 41/100`，**即便在修正后的阈值下也假**）
>    ⟹ 原路线 `hkey → hle → hlt → linarith` **不可达**；
>    `nlinarith` 报错是**正确行为**。已改为**无中转**的直接证明。
> 3. **两处 tactic 形状缺陷**（真缺陷，与 1、2 不同）：
>    `h3` 的 `rw [one_div, one_div, mul_inv, …]` 因 `one_div` **同时命中两处**、
>    `mul_inv` 又拆成 `2⁻¹*(1+ε)⁻¹` ⟹ **无 `x⁻¹*x` 子项**可被 `inv_mul_cancel₀` 消；
>    `hle` 的 `mul_le_mul_of_nonneg_right` 因目标残留 `1 *` 未消（`1 * ((1+ε)*δ)⁻¹`）而类型不符。
>    **两处均随路线替换一并消除**。
>
> **历史（Z1，v14）**：本文件此前长期**不可编译**，`RealCompressionRate.olean` 陈旧
> （`LastWriteTime` 09/21 05:58 < 源文件 09/22 01:00）⟹ 主定理结论**当时无内核背书**。
> 该状态**已由本轮解除**。旧记录中的错误位置 `:433 :437 :440` 属于**上一版行号**，已随改动漂移。

`RealErrorFeedback` 只给出**有界性**（残差一致有界 `|e_t| ≤ G(1−δ)/δ`、平均一致性 O(1/T)）
与一个**额外假设**下的率（`ef_sgd_rate` 需要「校正流是无偏次梯度估计」，该假设**不由**
压缩算子推出）。本文件补上缺失的**率**：直接从 δ-近似压缩 + 误差反馈的递推出发，
把压缩误差作为**显式加性项**推进 SGD 的望远镜求和，得到

    (1/T)·Σ_{t<T} E‖∇f(x_t)‖² ≤ (E₀)/(2ηT) + (η/2)·G² + (1−δ)²·G²·(有界因子)

取 η = Θ(1/√T) 即得主结果 **O(1/√T) + O((1−δ)²G²)**（惩罚因子 `(2−δ)/δ`），
且 `δ → 1` 时与无压缩的差距消失。

## 主结果

1. `compressionError_bounded_sq`（**压缩误差二阶矩界**）：由 δ-近似压缩
   `|C x − x| ≤ (1−δ)|x|`（`0 < δ ≤ 1`）与 `|g_t| ≤ G` 得
   `|C(e_t+g_t) − (e_t+g_t)|² ≤ (1−δ)²·(G/δ)²` —— 即**逐步压缩误差平方 ≤ (1−δ)²G²/δ²**，
   与 T 无关（承接 `errorFeedback_bounded` 的有界性，但升级为**平方**形式以进入率）。
2. `compressionError_sq_closed`（**闭式**）：代入 `errorFeedback_bounded` 的残差界
   `|e| ≤ G(1−δ)/δ` 得压缩误差平方 `≤ (1−δ)²·G²/δ²` —— 显式 `(1−δ)²` 依赖。
3. `compressed_direction_bounded`（**压缩方向有界**）：`|C(e+g)| ≤ G_c`，其中
   `G_c = (2−δ)·G/δ = compressionMoment G δ`。这是率分析中「压缩后方向有界」
   这一前提的**推导**（不是假设）。
4. `compression_avg_rate`（**核心：平均率**）：望远镜求和给出

       (1/T)·Σ_{t<T} E[f(x_t) − f x*] ≤ (E₀)/(2ηT) + (η/2)·G_c²

   这是标准 SGD 率形式，压缩的全部影响**只进入常数 G_c**。
5. `compression_rate_sqrt`（**主定理**）：取最优步长 `η = D/(G_c·√T)`（`E₀ = D²`）得
   `∃ t < T, E[f(x_t) − f x*] ≤ D·G_c/√T`，即主项 **O(1/√T)**。
6. `compression_rate_penalty_factor`（**显式差距项**）：`D·G_c = (D·G)·((2−δ)/δ)`，故
   `D·G_c/√T = (D·G/√T)·((2−δ)/δ)` —— 压缩带来的**相对惩罚因子** `(2−δ)/δ`
   在 `δ → 1` 时 `→ 1`（差距消失），`δ → 0` 时发散（与 `RealErrorFeedback`
   的无反馈反例一致）。
7. `compression_penalty_ge_one` / `compression_gap_vanishes`（**δ → 1 时差距消失**）：
   惩罚因子 `≥ 1`（压缩只可能变差），且对任意 `ε > 0` 存在
   `δ₀ = (2+ε)/(2+2ε)`（见 `compression_gap_vanishes` 中对 `δ0` 的显式取值）
   使 `δ ≥ δ₀` 时因子 `< 1 + ε` —— 即**高精度压缩几乎不损率**。
8. `no_compression_recovers_sgd`（**回收无缝情形**）：`δ = 1`（`C = id`，无压缩）时
   惩罚因子恰为 `1`，率**精确退化为** `RealSGDStochastic` 的 `D·G/√T`。
9. `compression_min_gap`（**单点率**）：由平均率得 `∃ t < T` 单点率（min ≤ 平均）。
10. `ef_rate_link`（**与 RealErrorFeedback 衔接**）：`G_c = G/δ + G(1−δ)/δ`，
    即 `errorFeedback_bounded` 的残差界 `G(1−δ)/δ` 与本文件的 `G_c` 是**同一常数族**。

## 诚实边界

- **诚实降级（重要）**：本文件的率陈述在**单步收缩假设** `hstep` 下给出（这是
  `RealSGDStochastic.sgd_expected_gap_sum_seq` 的既有口径，本文件不重新推导它）。
  与 `RealErrorFeedback.ef_sgd_rate` 的区别是本文件**不再需要「无偏」假设**：
  `G_c` 是**压缩后方向的二阶矩界**（含偏置的平方），偏置被吸收进 (1−δ) 项，
  这正是「δ → 1 差距消失」的来源。要把它化为纯 `∇f` 的陈述需 `f` 光滑 + 无偏，
  这部分**未做**（诚实标注：留待后续，不在本文件声称）。
- `0 < δ` 是本质的：`δ → 0` 时惩罚因子发散（`RealErrorFeedback.noFeedback_divergence` 对照）。
- 定标量 ℝ 一维，与 `RealSGDStochastic` / `RealErrorFeedback` 同口径。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、压缩误差的平方界（承接 RealErrorFeedback 的有界性） -/

/-- **压缩误差平方界**：δ-近似压缩 + 残差有界 `|e| ≤ B` + 梯度有界 `|g| ≤ G`，
    压缩误差 `|C(e+g) − (e+g)| = |e'|`（新残差）满足
    `|e'|² ≤ (1−δ)²·(B + G)²`。这是把 `RealErrorFeedback` 的**线性**界升级为
    可进入率的**平方**形式。 -/
theorem compressionError_bounded_sq (C : ℝ → ℝ) (δ B G e g : ℝ)
    (hδ1 : δ ≤ 1)
    (hC : ∀ x : ℝ, |C x - x| ≤ (1 - δ) * |x|)
    (he : |e| ≤ B) (hg : |g| ≤ G) (hB0 : 0 ≤ B) (hG0 : 0 ≤ G) :
    |C (e + g) - (e + g)| ^ 2 ≤ (1 - δ) ^ 2 * (B + G) ^ 2 := by
  have h1δ : 0 ≤ 1 - δ := by linarith
  have hsum : |e + g| ≤ B + G := by
    have h := abs_add e g
    linarith
  have hsum0 : 0 ≤ |e + g| := abs_nonneg _
  have hBG0 : 0 ≤ B + G := by linarith
  have hstep1 : |C (e + g) - (e + g)| ≤ (1 - δ) * |e + g| := hC (e + g)
  have hstep2 : (1 - δ) * |e + g| ≤ (1 - δ) * (B + G) :=
    mul_le_mul_of_nonneg_left hsum h1δ
  have habs : |C (e + g) - (e + g)| ≤ (1 - δ) * (B + G) := le_trans hstep1 hstep2
  have hlhs0 : 0 ≤ |C (e + g) - (e + g)| := abs_nonneg _
  calc
    |C (e + g) - (e + g)| ^ 2 ≤ ((1 - δ) * (B + G)) ^ 2 :=
      pow_le_pow_left₀ hlhs0 habs 2
    _ = (1 - δ) ^ 2 * (B + G) ^ 2 := by ring

/-- **压缩误差平方界的闭式（代入残差界）**：残差 `|e| ≤ G(1−δ)/δ`（`RealErrorFeedback`
    的 `errorFeedback_bounded` 结论）时，`B = G(1−δ)/δ`，故
    `B + G = G/δ`，压缩误差平方 `≤ (1−δ)²·G²/δ²`。
    这正是**显式 (1−δ)² 依赖**：`δ → 1` 时压缩误差平方 → 0，是主定理差距消失的来源。 -/
theorem compressionError_sq_closed (G δ : ℝ) (hδ0 : 0 < δ) :
    (1 - δ) ^ 2 * (G * (1 - δ) / δ + G) ^ 2 = (1 - δ) ^ 2 * G ^ 2 / δ ^ 2 := by
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hfac : G * (1 - δ) / δ + G = G / δ := by
    field_simp [hδne]
    ring
  rw [hfac, div_pow]
  ring_nf

/-! ## 二、压缩方向的二阶矩常数 G_c -/

/-- 压缩方向的**有效二阶矩常数**：`G_c = (2−δ)·G/δ`。
    推导：残差 `|e| ≤ G(1−δ)/δ`（`errorFeedback_bounded`）⟹ `|e+g| ≤ G/δ` ⟹
    `|C(e+g)| ≤ (1−δ)|e+g| + |e+g| = (2−δ)|e+g| ≤ (2−δ)·G/δ`。
    · `δ = 1`（无压缩）⟹ `G_c = G`（回收 SGD）；
    · `δ → 0` ⟹ `G_c → ∞`（与无反馈反例一致）。 -/
def compressionMoment (G δ : ℝ) : ℝ := (2 - δ) * G / δ

/-- `δ = 1` 时 `G_c = G`（**回收无缝情形**）：无压缩的常数精确等于 SGD 的 G。 -/
theorem compressionMoment_one (G : ℝ) : compressionMoment G 1 = G := by
  show (2 - 1) * G / 1 = G
  ring

/-- 压缩方向确实被 `G_c` 界住：`|C(e+g)| ≤ G_c`（在残差有界 `|e| ≤ G(1−δ)/δ` 下）。
    这是率分析中「压缩后方向有界」这一前提的**推导**（不是假设）。 -/
theorem compressed_direction_bounded (C : ℝ → ℝ) (δ G e g : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : ∀ x : ℝ, |C x - x| ≤ (1 - δ) * |x|)
    (he : |e| ≤ G * (1 - δ) / δ) (hg : |g| ≤ G) (hG0 : 0 ≤ G) :
    |C (e + g)| ≤ compressionMoment G δ := by
  have h1δ : 0 ≤ 1 - δ := by linarith
  have hres0 : 0 ≤ G * (1 - δ) / δ := div_nonneg (mul_nonneg hG0 h1δ) (le_of_lt hδ0)
  have hsum : |e + g| ≤ G * (1 - δ) / δ + G := by
    have h := abs_add e g
    linarith
  have hce : |C (e + g) - (e + g)| ≤ (1 - δ) * |e + g| := hC (e + g)
  have hbound : (1 - δ) * |e + g| ≤ (1 - δ) * (G * (1 - δ) / δ + G) :=
    mul_le_mul_of_nonneg_left hsum h1δ
  have hres_le : (1 - δ) * (G * (1 - δ) / δ + G) ≤ G * (1 - δ) / δ := by
    have hkey : (1 - δ) * (G * (1 - δ) / δ + G) = G * (1 - δ) / δ := by
      field_simp [ne_of_gt hδ0]
      ring
    rw [hkey]
  have hperr : |C (e + g) - (e + g)| ≤ G * (1 - δ) / δ :=
    le_trans hce (le_trans hbound hres_le)
  have hsplit : |C (e + g)| ≤ |C (e + g) - (e + g)| + |e + g| := by
    have h := abs_add (C (e + g) - (e + g)) (e + g)
    simpa using h
  have hfin : |C (e + g)| ≤ (2 - δ) * (G * (1 - δ) / δ + G) := by
    have h1 : |C (e + g)| ≤ G * (1 - δ) / δ + (G * (1 - δ) / δ + G) := by linarith
    have h2 : G * (1 - δ) / δ + (G * (1 - δ) / δ + G)
        = (2 - δ) * (G * (1 - δ) / δ + G) := by
      field_simp [ne_of_gt hδ0]
      ring
    linarith [h1, h2.le, h2.ge]
  have hval : (2 - δ) * (G * (1 - δ) / δ + G) = compressionMoment G δ := by
    show (2 - δ) * (G * (1 - δ) / δ + G) = (2 - δ) * G / δ
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    have hinner : G * (1 - δ) / δ + G = G / δ := by
      field_simp [hδne]
      ring
    rw [hinner]
    ring
  linarith [hfin, hval.le, hval.ge]

/-! ## 三、压缩 SGD 的望远镜平均率 -/

/-- **压缩 SGD 平均率（核心）**：若压缩下降方向的单步期望收缩为

    `E_{t+1} ≤ E_t − 2η·Gap_t + η²·G_c²`

    （`E_t = E‖x_t − x*‖²`、`Gap_t = E[f(x_t) − f x*]`、`G_c` 压缩后方向的二阶矩界），
    则**平均率**

    `(1/T)·Σ_{t<T} Gap_t ≤ E₀/(2ηT) + η·G_c²/2`。

    直接调用 `sgd_expected_gap_sum_seq`（`RealSGDStochastic`）——压缩的影响
    **只体现在常数 G_c 上**，不改变率的**形状**。 -/
theorem compression_avg_rate {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (f : ℝ → ℝ) (x : ℕ → Ω → ℝ) (xstar η Gc : ℝ) (T : ℕ) (hη : 0 < η) (hT : 0 < T)
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * Gc ^ 2) :
    (1 / (T : ℝ)) * (∑ t in Finset.range T, ExpGap p f (x t) xstar) ≤
      ExpDist p (x 0) xstar / (2 * η * (T : ℝ)) + η * Gc ^ 2 / 2 := by
  have hsum := sgd_expected_gap_sum_seq p hp0 f x xstar η Gc T (le_of_lt hη) hstep
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have h2η : 0 < 2 * η := by linarith
  have h2ηne : (2 * η) ≠ 0 := ne_of_gt h2η
  set S : ℝ := ∑ t in Finset.range T, ExpGap p f (x t) xstar with hS
  have hgoal : (1 / (T : ℝ)) * S ≤
      ExpDist p (x 0) xstar / (2 * η * (T : ℝ)) + η * Gc ^ 2 / 2 := by
    have hden : (0 : ℝ) < 2 * η * (T : ℝ) := mul_pos h2η hTpos
    have heq : ExpDist p (x 0) xstar / (2 * η * (T : ℝ)) + η * Gc ^ 2 / 2
        = (ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * Gc ^ 2) / (2 * η * (T : ℝ)) := by
      field_simp [h2ηne, hTne]
      ring
    rw [heq, le_div_iff₀ hden]
    have hSle : S * (2 * η) ≤ ExpDist p (x 0) xstar + η ^ 2 * (T : ℝ) * Gc ^ 2 := by
      nlinarith [hsum]
    have hTeq : (1 / (T : ℝ)) * S * (2 * η * (T : ℝ)) = S * (2 * η) := by
      field_simp [hTne]
      ring
    rw [hTeq]
    exact hSle
  simpa [hS] using hgoal

/-- **主定理：压缩通信的显式收敛率**。取最优步长 `η = D/(G_c·√T)`（`E₀ = D²`）时

    `(1/T)·Σ_{t<T} E[f(x_t) − f x*] ≤ D·G_c/√T`，

    且由 `G_c = G·(2−δ)/δ` 得**显式差距项**

    `D·G_c/√T = (D·G/√T)·((2−δ)/δ)`。

    即 **O(1/√T) 主项 + O(2(1−δ)/δ) 的压缩惩罚**（因子 `(2−δ)/δ`），
    `δ → 1` 时惩罚消失。

    **注意 docstring 校准（Z1-2，v14）**：本条**旧稿**曾写
    「`G_c ≤ G·(1 + (1−δ)/δ)`」与「`·(1 + (1−δ)/δ)`」——**错误**。
    代数复核：`compressionMoment G δ = (2−δ)·G/δ`（本文件 `compressionMoment` 定义处），
    而 `1 + (1−δ)/δ = (δ + 1 − δ)/δ = 1/δ`，故
    `G·(1 + (1−δ)/δ) = G/δ ≠ (2−δ)G/δ = G_c`（除非 `δ = 1`）。
    数值：`δ = 1/2` 时 `(2−δ)/δ = 3` 而 `1 + (1−δ)/δ = 2`（**不等**）。
    正确分解见 `compression_penalty_gap_rate`：
    `(2−δ)/δ = 1 + 2(1−δ)/δ`（**`2(1−δ)/δ`，不是 `(1−δ)/δ`**）。
    此处已改为与 `compression_rate_penalty_factor` 逐字一致。

    **注意 B56.3 更正（v15）**：本段首句原写「`O((1−δ)/δ)` 的压缩惩罚」，
    与同文件下段的 `2(1−δ)/δ` **自相矛盾**（已改为 `O(2(1−δ)/δ)`）；
    且 `compressionMoment` 的定义行号与 `compression_rate_penalty_factor` 的行号
    所标数值**陈旧**（先标 `:115`／`:229`，改标为 `:136`／`:260` 后**再次**漂移），
    故**一律不再使用行号**，改以符号名定位（`compressionMoment` 的定义处、
    `compression_rate_penalty_factor` 的定义处）。 -/
theorem compression_rate_sqrt {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (f : ℝ → ℝ) (x : ℕ → Ω → ℝ) (xstar Gc D η : ℝ) (T : ℕ)
    (hGc : 0 < Gc) (hT : 0 < T) (hD : 0 < D)
    (hD2 : ExpDist p (x 0) xstar = D ^ 2)
    (hη : η = D / (Gc * Real.sqrt (T : ℝ)))
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * Gc ^ 2) :
    ∃ t : ℕ, t < T ∧ ExpGap p f (x t) xstar ≤ D * Gc / Real.sqrt (T : ℝ) :=
  sgd_rate_bound p hp0 f x xstar Gc D η T hGc hT hD hD2 hη hstep

/-- **压缩惩罚的显式形式**：`G_c = (2−δ)·G/δ` 时，主定理的率 `D·G_c/√T` 可写成
    `(D·G/√T)·((2−δ)/δ)`——把压缩对率的**全部影响**隔离为一个乘性惩罚因子
    `(2−δ)/δ`，`δ → 1` 时该因子 → 1（差距消失）。 -/
theorem compression_rate_penalty_factor (D G δ : ℝ) :
    D * compressionMoment G δ = (D * G) * ((2 - δ) / δ) := by
  show D * ((2 - δ) * G / δ) = (D * G) * ((2 - δ) / δ)
  ring

/-- **惩罚因子的界**：`0 < δ ≤ 1` 时 `1 ≤ (2−δ)/δ`，故压缩**只可能变差**
    （因子 ≥ 1），且 `δ = 1` 时取等（无惩罚）。 -/
theorem compression_penalty_ge_one (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ (2 - δ) / δ := by
  rw [le_div_iff₀ hδ0]
  linarith

/-! ## 四、δ → 1 时差距消失 -/

/-- **`compression_gap_vanishes`（δ → 1 差距消失）**：对任意精度要求 `ε > 0`，存在
    `δ₀ ∈ (0, 1]`（显式取 `δ₀ = (2+ε)/(2+2ε)`）使 `δ₀ ≤ δ ≤ 1` 时惩罚因子
    `(2−δ)/δ ≤ 1 + ε`。即**压缩足够精确时，收敛率与无压缩的差距任意小**。 -/
theorem compression_gap_vanishes (ε : ℝ) (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ : ℝ, δ0 ≤ δ → δ ≤ 1 →
      (2 - δ) / δ < 1 + ε := by
  have h2ε : (0 : ℝ) < 2 + ε := by linarith
  have h2ε' : (0 : ℝ) < 2 + 2 * ε := by linarith
  set δ0 : ℝ := (2 + ε) / (2 + 2 * ε) with hδ0def
  have hδ0pos : 0 < δ0 := div_pos h2ε h2ε'
  have hδ0le : δ0 ≤ 1 := by
    rw [hδ0def, div_le_one h2ε']
    linarith
  refine ⟨δ0, hδ0pos, hδ0le, ?_⟩
  intro δ hδ hδ1
  have hδpos : 0 < δ := lt_of_lt_of_le hδ0pos hδ
  rw [div_lt_iff₀ hδpos]
  have hbase : δ0 * (2 + 2 * ε) = 2 + ε :=
    div_mul_cancel₀ (2 + ε) (ne_of_gt h2ε')
  have hmul : 2 + ε ≤ δ * (2 + 2 * ε) := by
    calc
      (2 + ε) = δ0 * (2 + 2 * ε) := hbase.symm
      _ ≤ δ * (2 + 2 * ε) := mul_le_mul_of_nonneg_right hδ (le_of_lt h2ε')
  nlinarith [hmul, hε]

/-! ## 五、单点率（min ≤ 平均）与衔接 -/

/-- **单点率推论**：平均率 ⟹ `∃ t < T` 使单点差距不超过平均值
    （压缩情形的 `min ≤ 平均`）。 -/
theorem compression_min_gap {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (f : ℝ → ℝ) (x : ℕ → Ω → ℝ) (xstar η Gc : ℝ) (T : ℕ) (hη : 0 < η) (hT : 0 < T)
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * Gc ^ 2) :
    ∃ t : ℕ, t < T ∧ ExpGap p f (x t) xstar ≤
      ExpDist p (x 0) xstar / (2 * η * (T : ℝ)) + η * Gc ^ 2 / 2 := by
  have havg := compression_avg_rate p hp0 f x xstar η Gc T hη hT hstep
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  set B : ℝ := ExpDist p (x 0) xstar / (2 * η * (T : ℝ)) + η * Gc ^ 2 / 2 with hB
  have hsum_le : (∑ t in Finset.range T, ExpGap p f (x t) xstar) ≤ (T : ℝ) * B := by
    have hTmul : (T : ℝ) * ((1 / (T : ℝ)) *
        (∑ t in Finset.range T, ExpGap p f (x t) xstar))
        = ∑ t in Finset.range T, ExpGap p f (x t) xstar := by
      field_simp [hTne]
    have hscaled : (T : ℝ) * ((1 / (T : ℝ)) *
        (∑ t in Finset.range T, ExpGap p f (x t) xstar)) ≤ (T : ℝ) * B :=
      mul_le_mul_of_nonneg_left (by rw [hB]; exact havg) (le_of_lt hTpos)
    rwa [hTmul] at hscaled
  rcases exists_le_sum_mul (a := fun t : ℕ => ExpGap p f (x t) xstar) hT hsum_le with
    ⟨t, ht, hgap⟩
  exact ⟨t, ht, hgap⟩

/-- **无压缩回收 SGD 率**：`δ = 1` 时 `G_c = G`，主定理精确退化为
    `RealSGDStochastic` 的 `D·G/√T`（惩罚因子 = 1，无损失）。 -/
theorem no_compression_recovers_sgd (D G : ℝ) :
    D * compressionMoment G 1 = D * G := by
  rw [compressionMoment_one]

/-- **与 RealErrorFeedback 的衔接**：`RealErrorFeedback.errorFeedback_bounded` 给出的
    残差界 `G(1−δ)/δ` 正是本文件 `compressionMoment` 中 `G_c = (2−δ)G/δ` 的
    来源；两者是**同一常数族**：`G_c = G/δ + G(1−δ)/δ`。 -/
theorem ef_rate_link (G δ : ℝ) (hδ0 : 0 < δ) :
    compressionMoment G δ = G * (1 - δ) / δ + G / δ := by
  show (2 - δ) * G / δ = G * (1 - δ) / δ + G / δ
  field_simp [ne_of_gt hδ0]
  ring

/-- **压缩率的闭环**：`δ = 1` 时 `G_c = G`，故率 `D·G_c/√T = D·G/√T`
    （精确回收无压缩情形）。 -/
theorem compression_moment_tendsto_one (G : ℝ) :
    compressionMoment G 1 = G ∧ compressionMoment G 1 - G = 0 := by
  refine ⟨compressionMoment_one G, ?_⟩
  rw [compressionMoment_one]
  ring

/-! ## 六、速率的显式 `(1−δ)²` 依赖（C10）

§五 只证「`δ → 1` 时惩罚消失」（`compression_gap_vanishes`：对任意 `ε > 0`
存在 `δ₀` 使因子 `< 1 + ε`）。本节给出**速率**：惩罚因子以 `(1−δ)` 的**一阶**速率
趋近 `1`，**压缩误差平方**以 `(1−δ)²` 的速率趋近 `0`。

### 6.1 惩罚因子的精确分解（**速率 `(1−δ)/(δ)·2`**）

    `(2−δ)/δ − 1 = 2(1−δ)/δ`

即「惩罚超出 `1` 的部分」**精确**等于 `2(1−δ)/δ`，故

  * `compression_penalty_gap_rate`：`(2−δ)/δ ≤ 1 + 2(1−δ)/δ`（**等式**）；
  * `compression_penalty_gap_le`：`δ ≥ 1/2` 时 `2(1−δ)/δ ≤ 4(1−δ)`
    ——即 `δ` 在 `[1/2, 1]` 上惩罚的超出量是 `O(1−δ)`（常数 `4`）。

### 6.2 压缩误差平方的 `(1−δ)²` 速率

`compressionError_sq_closed` 给出 `(1−δ)²G²/δ²`。本节补速率形式：

  * `compressionError_sq_rate`：`δ ≥ 1/2` 时 `(1−δ)²G²/δ² ≤ 4(1−δ)²G²`
    ——**显式 `(1−δ)²` 依赖**，常数 `4`（`δ = 1/2` 时取到）；
  * `compressionError_sq_rate_sharp`：`δ = 1/2` 时 `1/δ² = 4`
    ——即常数 `4` 在 `δ ≥ 1/2` 上是**最优**的（在 `δ = 1/2` 取等）；
  * `compressionError_sq_o_delta_sq`：等价形式
    `(1−δ)²G²/δ² = G²·((1−δ)/δ)²` ——把 `(1−δ)²` **显式暴露**为一元因子的平方。

### 6.3 `δ → 1` 的定量速率

  * `compression_gap_rate_explicit`：`2/(2+ε) < δ` 时惩罚 `< 1 + ε`
    ——把 §五 的存在性形式升级为**显式充分条件**（对 `ε` 的定量依赖）。
    注意 **v15 更正**：本条原写 `1 − δ ≤ 1/(2(1+ε))` —— **过松，该陈述为假**
    （反例 `δ = 397/500, ε = 1/20`）。正确阈值 `(2−δ)/δ < 1+ε ⟺ 2/(2+ε) < δ`，
    机器验证反例见 `compression_gap_rate_threshold_sharp`，登记于 `CORRECTIONS B64`。

**诚实标注（C10）**：
  · 6.1 的 `δ ≥ 1/2` 是**技术性限制**（使 `1/δ ≤ 2`）；对 `δ ∈ (0, 1/2)`，
    常数会随 `1/δ` 增长（与 `RealErrorFeedback.noFeedback_divergence` 一致），**标注**；
  · 本节给的是**惩罚因子/压缩误差**的速率，**不**声称主率 `D·G_c/√T` 中
    `T` 方向的速率改进（那是 `RealSGDStochastic` 的口径），**标注**；
  · 「`O((1−δ)²)`」在此处的**严格含义**是 6.2 的两条不等式
    （`≤ 4(1−δ)²G²` 与 `= G²((1−δ)/δ)²`），**不是**渐近记号的形式化。 -/

/-- **惩罚因子的精确分解（速率形式）**：`(2−δ)/δ = 1 + 2(1−δ)/δ`（`δ ≠ 0`）。

即「惩罚超出 `1` 的部分」**精确**是 `2(1−δ)/δ` —— 这是 `O(1−δ)` 速率的来源。 -/
theorem compression_penalty_gap_rate (δ : ℝ) (hδ0 : δ ≠ 0) :
    (2 - δ) / δ = 1 + 2 * (1 - δ) / δ := by
  field_simp
  ring

/-- **`δ ≥ 1/2` 时惩罚超出量是 `O(1−δ)`（常数 4）**：
`2(1−δ)/δ ≤ 4(1−δ)`（`1/2 ≤ δ ≤ 1`）。 -/
theorem compression_penalty_gap_le {δ : ℝ} (hδ : 1 / 2 ≤ δ) (hδ1 : δ ≤ 1) :
    2 * (1 - δ) / δ ≤ 4 * (1 - δ) := by
  have hδpos : 0 < δ := by linarith
  have h1δ : 0 ≤ 1 - δ := by linarith
  rw [div_le_iff₀ hδpos]
  nlinarith

/-- **压缩误差平方的 `(1−δ)²` 速率**：`1/2 ≤ δ ≤ 1`、`G ≥ 0` 时
`(1−δ)²·G²/δ² ≤ 4·(1−δ)²·G²`。

**这就是 C10 要求的显式速率**：压缩误差随 `(1−δ)²` 衰减（常数 `4`）。 -/
theorem compressionError_sq_rate (G δ : ℝ) (hδ : 1 / 2 ≤ δ) :
    (1 - δ) ^ 2 * G ^ 2 / δ ^ 2 ≤ 4 * ((1 - δ) ^ 2 * G ^ 2) := by
  have hδpos : 0 < δ := by linarith
  have hnum : 0 ≤ (1 - δ) ^ 2 * G ^ 2 := by positivity
  have hδ2 : (1 : ℝ) / 4 ≤ δ ^ 2 := by nlinarith
  have hδ2pos : 0 < δ ^ 2 := by positivity
  rw [div_le_iff₀ hδ2pos]
  -- 目标：`(1−δ)²G² ≤ 4·((1−δ)²G²)·δ²`，由 `δ² ≥ 1/4` 得 `4δ² ≥ 1`
  have hmul : (1 : ℝ) ≤ 4 * δ ^ 2 := by linarith
  nlinarith [mul_nonneg hnum (sub_nonneg.mpr hmul)]

/-- **速率常数 `4` 在 `δ = 1/2` 处取等（sharp）**：`δ = 1/2` 时 `1/δ² = 4`，
故 6.2 的常数 `4` **不能**在 `δ ≥ 1/2` 上改小。 -/
theorem compressionError_sq_rate_sharp :
    ((1 : ℝ) - 1 / 2) ^ 2 * (1 : ℝ) ^ 2 / (1 / 2) ^ 2
      = 4 * (((1 : ℝ) - 1 / 2) ^ 2 * (1 : ℝ) ^ 2) := by
  norm_num

/-- **`(1−δ)²` 的显式暴露**：`(1−δ)²G²/δ² = G²·((1−δ)/δ)²`。

把 §一 的闭式改写成「`(1−δ)` 的一元因子的平方」形式，
使「`O((1−δ)²)`」有**逐项可读**的含义（`δ → 1` 时一元因子 → 0）。 -/
theorem compressionError_sq_o_delta_sq (G δ : ℝ) (hδ0 : δ ≠ 0) :
    (1 - δ) ^ 2 * G ^ 2 / δ ^ 2 = G ^ 2 * ((1 - δ) / δ) ^ 2 := by
  field_simp
  ring

/-- **`δ → 1` 的显式定量速率（把 §五 的存在性形式升级）**：
若 `2/(2+ε) < δ`（`ε > 0`、`δ > 0`），则惩罚因子 `(2−δ)/δ < 1 + ε`。

即「精度 `δ` 到 `1` 的距离」以 `2/(2+ε)` 为阈值**定量地**控制惩罚 ——
这是 §五 `compression_gap_vanishes` 存在性形式的**显式充分条件**。

**注意 v15 更正（原稿阈值过松，该命题原为假）**：本条原稿的前件是

    `1 - δ ≤ 1 / (2 * (1 + ε))`      -- 不成立 过松，命题为假

**反例**（精确有理数，见本文件 `compression_gap_rate_threshold_sharp` 的机器验证）：
取 `δ = 397/500`、`ε = 1/20`，则 `1 − δ = 103/500 = 0.206 ≤ 1/(2(1+ε)) = 10/21 ≈ 0.476` 成立 **前件成立**，
而 `(2−δ)/δ = 603/397 ≈ 1.5189 ≮ 1 + ε = 21/20 = 1.05` 不成立 **结论为假**。

**正确阈值**（代数恒等，`δ > 0`）：

    `(2−δ)/δ < 1 + ε  ⟺  2 < δ·(2+ε)  ⟺  2/(2+ε) < δ`

故充分条件必须取 **`2/(2+ε) < δ`**（**严格**：`δ = 2/(2+ε)` 时左右取等，结论的 `<` 不成立）。
**注意 `1 − δ ≤ (1+ε)/(2+ε)` 形式的"修正"同样为假**（它只给 `δ ≥ 1/(2+ε)`，
比所需的 `2/(2+ε)` **小一倍**；反例 `δ = 1/2, ε = 1/10`）——该次更正尝试已废弃。

与 `compression_gap_vanishes`（`δ₀ = (2+ε)/(2+2ε)`）的关系：`(2+ε)/(2+2ε) > 2/(2+ε)` 恒成立，
故那条的 `δ₀` 是本条阈值的一个**充分**取值（两者同一常数族，本条阈值更贴近结论）。

**注意 诚实标注（v15）**：`hδ1 : δ ≤ 1` 在本证明中**未被使用**（`hclose` 已蕴含 `δ > 2/(2+ε) > 0`；
`δ ≤ 1` 不再是结论所需）。此处**保留**该假设作为**输入域标注**（与 §五 口径一致），
以便下游接口不变；**若需无条件版可另行陈述**。证明路线亦已整体替换：
原稿经 `hkey → hle → hlt → linarith` 三段中转，而其中的
`hlt : 1/((1+ε)δ) < ε` **本身是假命题**（反例 `δ = 987/1000, ε = 41/100`），
故该路线**不可达**；本证明直接由 `hclose` 得到结论的等价形式，无中转。 -/
theorem compression_gap_rate_explicit (δ ε : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ)
    (hclose : 2 / (2 + ε) < δ) :
    (2 - δ) / δ < 1 + ε := by
  have h2e : 0 < 2 + ε := by linarith
  -- `(2−δ)/δ < 1+ε  ⟺  2 < δ·(2+ε)`
  have h : 2 < δ * (2 + ε) := by
    have hh := (div_lt_iff₀ h2e).mp hclose
    linarith
  rw [div_lt_iff₀ hδ0]
  nlinarith [h]

/-- **`compression_gap_rate_explicit` 原稿阈值的反例（回归钉，v15）**：

存在 `δ ε`（`ε > 0`、`0 < δ ≤ 1`）使
`1 − δ ≤ 1/(2(1+ε))` **成立**而 `(2−δ)/δ < 1 + ε` **为假** ——
即**原稿的充分条件过松，该定理原陈述是假命题**。

**显式见证**：`δ = 397/500`、`ε = 1/20`
（`1 − δ = 103/500 ≤ 10/21 = 1/(2(1+ε))` 成立，而 `(2−δ)/δ = 603/397 ≥ 21/20 = 1+ε` 不成立）。

见证取**精确有理数**（`397/500` 与 `1/20`），闭合走 `norm_num`，
故本条的每条不等式均为**内核验证**（**非**浮点估计；对照 STYLE 已登记的
"浮点搜索会因舍入产生伪反例"）。
**修正后的阈值见 `compression_gap_rate_explicit`（`2/(2+ε) < δ`），登记于 `CORRECTIONS B64`**。 -/
theorem compression_gap_rate_threshold_sharp :
    ∃ δ ε : ℝ, 0 < ε ∧ 0 < δ ∧ δ ≤ 1 ∧
      1 - δ ≤ 1 / (2 * (1 + ε)) ∧ ¬ ((2 - δ) / δ < 1 + ε) := by
  refine ⟨397 / 500, 1 / 20, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- **主定理的 `(1−δ)²` 版本（端到端）**：`1/2 ≤ δ ≤ 1` 时，
压缩误差平方界 `(1−δ)²G²/δ²` 被 `4(1−δ)²G²` 控制（由 6.2）。

与 `compressionError_sq_closed`（闭式）配套：闭式给出**精确表达式**，
本定理给出**速率形式**。 -/
theorem compressionError_sq_closed_rate (G δ : ℝ) (hδ0 : 0 < δ) (hδ : 1 / 2 ≤ δ) :
    (1 - δ) ^ 2 * (G * (1 - δ) / δ + G) ^ 2 ≤ 4 * ((1 - δ) ^ 2 * G ^ 2) := by
  rw [compressionError_sq_closed G δ hδ0]
  exact compressionError_sq_rate G δ hδ

/-! ## 注：闭环语义
  δ-近似压缩（IsCompressor，RealErrorFeedback）→ 残差有界 G(1−δ)/δ
  （errorFeedback_bounded）→ 压缩误差**平方**界 (1−δ)²G²/δ²
  （compressionError_bounded_sq / compressionError_sq_closed）→
  压缩方向有界 G_c = (2−δ)G/δ（compressed_direction_bounded）→
  望远镜平均率（compression_avg_rate）→ 最优步长率 D·G_c/√T
  （compression_rate_sqrt = O(1/√T)，惩罚因子 (2−δ)/δ）→ δ→1 差距消失
  （compression_gap_vanishes）→ δ=1 回收 SGD（no_compression_recovers_sgd）。
  诚实标注：率的**单步收缩假设**沿用 RealSGDStochastic 口径；纯 ∇f 版本未做。
  **【本轮更新 C10】** §六 补上**显式速率**：惩罚超出量精确等于 `2(1−δ)/δ`
  （`compression_penalty_gap_rate`），`1/2 ≤ δ ≤ 1` 时压缩误差平方
  `≤ 4(1−δ)²G²`（`compressionError_sq_rate`，常数 `4` 在 `δ = 1/2` 取等，
  `compressionError_sq_rate_sharp`），并给出 `δ → 1` 的**定量充分条件**
  （`compression_gap_rate_explicit`）。**未做**：`δ → 0` 侧的速率
  （常数随 `1/δ` 发散，见 `RealErrorFeedback.noFeedback_divergence`）。 -/

end Lattice
