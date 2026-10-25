import Mathlib

/-!
# LATTICE: 均匀量化的误差界与二阶矩刻画（训练系统方向，W8-5）

## 建立什么

**均匀（affine）量化**：格点间距 `Δ > 0`，量化器 `Q` 满足**误差契约**
`|Q x - x| ≤ Δ/2`（对落在格内的一切 `x`）。本文件证明五条**互不重述**的结果：

1. `quant_err_sharp_witness`：`Δ/2` 是 **sharp** 常数——`x = Δ/2`（两格点中点）时
   `|0 - Δ/2| = Δ/2`，**上界被取到**，常数不可收紧；
2. `quant_err_bitwidth`：`Δ = (hi-lo)/(2^b - 1)`（`b ≥ 1` 位、范围 `[lo,hi]`）⟹
   `|Q x - x| ≤ (hi-lo)/(2(2^b - 1))`；
3. `quant_bitwidth_rate`：**加 1 位使步长至少减半**——`Δ(b+1) ≤ Δ(b)/2`；
4. ⭐ `quant_mse_bound`（核心）：在**有限概率空间**上，
   `E[(Q(x) - x)²] ≤ Δ²/4`（**与分布无关**的一致界）；
5. ⭐ `quant_mse_zero_iff`：`Σ_w (Q w - x w)² = 0` ⟺ `Q w = x w` **处处**
   ——**退化解的完整刻画**，由此**排除**「存在一个使误差最小的非平凡分布」这一误读。

## 依赖什么

纯 `Mathlib`（有限概率空间上的 `Finset` 求和）。**不** import 任何 LATTICE 模块，
保持**零耦合**。

## 不做什么（诚实边界）

- **不**构造量化算法（`round` 的实现、tie-breaking 规则）：`Q` 是**抽象**映射，
  只用到误差契约；
- **不**涉及 per-channel / per-group 量化（见 `RealQAT`、`RealMixedPrecision`）；
- **不**涉及**随机**舍入的无偏性（见 `RealSTEError`）；
- **不**声称量化误差与训练损失的端到端关系（`RealQATRate` 的范围）；
- ⚠ **不**把「均匀分布最优」写成「MSE 最小」：MSE 是分布的**泛函**，
  退化（无失真）分布使之为 `0`。本文件用 `quant_mse_zero_iff`
  **刻画**零误差的充要条件，而**不**声称「存在最小化 MSE 的最优分布」。

## ⚠ 边界取等检查

- `Δ = 0`：`|Q x - x| ≤ 0` 只在格点上可满足；本文件所有界带 `0 < Δ`。
- `Δ/2` **取等可发生**：`x = Δ/2` 时 `|Q x - x| = Δ/2`（`quant_err_sharp_witness`）。
- `b ≥ 1` **不可省**：`b = 0` 时 `2^0 - 1 = 0`，`Δ` 是除零垃圾值。
- `lo ≤ hi` **不可省**：`lo > hi` 时 `Δ < 0`，`|Q x - x| ≤ Δ/2 < 0` 与绝对值非负
  **矛盾** ⟹ 契约假设不可满足 ⟹ 含契约的定理在那时**空洞**。故显式带 `hlo`。
- ⚠ **`Δ²/4` 不是 `Δ²/12`**：`Δ²/12` 是**均匀分布**下端到端误差的精确二阶矩，
  但它**不是**一致上界。本文件给**一致**界 `Δ²/4`，并**明确不声称**
  `Δ²/12` 对所有分布成立（那是**假**的：取 `x` 恒为 `Δ/2`、`Q x = 0`
  得 `E[(Qx-x)²] = Δ²/4 > Δ²/12`）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、逐点误差界及其 sharpness -/

/-- **`Δ/2` 是 sharp 常数：上界被取到**。

取 `Δ > 0`、`x := Δ/2`、`Q x := 0`（`0` 与 `Δ` 的中点，最近格点任取其一），
则 `|Q x - x| = Δ/2`。

**它比定义多说了什么**：单有「`≤ Δ/2`」不能排除常数可收紧到 `Δ/2 - ε`；
本定理用**显式构造**排除之。`0 < Δ` 使 `Δ/2 > 0`，从而 `|0 - Δ/2| = Δ/2`
的绝对值化简可用；`Δ ≤ 0` 时该等式与绝对值非负**矛盾**，故见证必须有 `0 < Δ`。 -/
theorem quant_err_sharp_witness (Δ : ℝ) (hΔ : 0 < Δ) :
    |(0 : ℝ) - Δ / 2| = Δ / 2 := by
  rw [zero_sub, abs_neg, abs_of_pos (by linarith : (0:ℝ) < Δ / 2)]

/-- **位宽 — 误差的显式关系**：`b ≥ 1`、`lo ≤ hi`、`Δ = (hi-lo)/(2^b - 1)`、
`|Q x - x| ≤ Δ/2` ⟹ `|Q x - x| ≤ (hi-lo)/(2·(2^b - 1))`。

**它比定义多说了什么**：把抽象的 `Δ/2` 化为**可调的位宽 `b`**。
⚠ **`b ≥ 1` 不可省**（`b = 0` 时 `2^0 - 1 = 0`，除零）。

⚠ **`hlo : lo ≤ hi` 的诚实定位（不是承重假设）**：**去掉 `hlo` 后本定理仍完整可证**
（判据：`hlo` 在 `quant_err_bitwidth` 的证明体中**从未被引用**，可逐行核对；
故 Lean **不会**报 `unused variable 'hlo'`——该假设出现在定理签名中，linter 不对其告警，
**不可**以 linter 警告当作判据）；`lo > hi` 时 `Δ < 0`，
契约 `hQ : |Q x - x| ≤ Δ/2` 因右端为负而**不可满足** ⟹ 定理在该处**空洞真**，
**并非**"靠 `hlo` 才成立"。保留 `hlo` 的用途是**契约可满足性的语义标注**
（`Δ ≥ 0`，量化步长非负），**不是必要前提**。 -/
theorem quant_err_bitwidth (Δ x hi lo : ℝ) (b : ℕ) (Q : ℝ → ℝ) (hb : 1 ≤ b)
    (hlo : lo ≤ hi) (hΔeq : Δ = (hi - lo) / (2 ^ b - 1)) (hQ : |Q x - x| ≤ Δ / 2) :
    |Q x - x| ≤ (hi - lo) / (2 * (2 ^ b - 1)) := by
  have hb0 : b ≠ 0 := by omega
  have hpow : (1 : ℝ) < 2 ^ b := by exact_mod_cast Nat.one_lt_two_pow hb0
  have hden : (2 : ℝ) ^ b - 1 ≠ 0 := by
    have : (0 : ℝ) < 2 ^ b - 1 := by linarith
    exact ne_of_gt this
  calc |Q x - x| ≤ Δ / 2 := hQ
    _ = (hi - lo) / (2 ^ b - 1) / 2 := by rw [hΔeq]
    _ = (hi - lo) / ((2 ^ b - 1) * 2) := by rw [div_div]
    _ = (hi - lo) / (2 * (2 ^ b - 1)) := by rw [mul_comm]

/-- **加 1 位使步长至少减半**：`b ≥ 1`、`lo ≤ hi` ⟹
`(hi-lo)/(2^{b+1}-1) ≤ (hi-lo)/(2^b - 1)/2`。

**它比定义多说了什么**：把「每位 1 bit」的**精度提升速率**写成**显式不等式**——
`Δ(b+1) ≤ Δ(b)/2`，即误差**至少**减半（因为 `2(2^b-1) ≤ 2^{b+1}-1`，
差值 `2^b - 1 ≥ 0` 是格点数非线性增长带来的**额外**收益）。

**证明**：化为 `2(2^b-1) ≤ 2^{b+1}-1`（对 `hi - lo ≥ 0` 与正分母做乘出）。

**注意** **`0 ≤ hi - lo` 不可省**：`hi < lo` 时两侧同乘负数，**不等号反转**。 -/
theorem quant_bitwidth_rate (hi lo : ℝ) (b : ℕ) (hb : 1 ≤ b) (hlo : lo ≤ hi) :
    (hi - lo) / (2 ^ (b + 1) - 1) ≤ (hi - lo) / (2 ^ b - 1) / 2 := by
  have hb0 : b ≠ 0 := by omega
  have hpow : (1 : ℝ) < 2 ^ b := by exact_mod_cast Nat.one_lt_two_pow hb0
  have hden : 0 < (2 : ℝ) ^ b - 1 := by linarith
  have hden' : 0 < (2 : ℝ) ^ (b + 1) - 1 := by
    have h2 : (1 : ℝ) < 2 ^ (b + 1) := by
      have hb1 : b + 1 ≠ 0 := by omega
      exact_mod_cast Nat.one_lt_two_pow hb1
    linarith
  have hstep : 2 * ((2 : ℝ) ^ b - 1) ≤ (2 : ℝ) ^ (b + 1) - 1 := by
    have hp : (2 : ℝ) ^ (b + 1) = 2 ^ b * 2 := by rw [pow_succ]
    have h2 : (1 : ℝ) ≤ 2 ^ b := le_of_lt hpow
    rw [hp]; linarith
  have hkey : 1 / ((2 : ℝ) ^ (b + 1) - 1) ≤ 1 / ((2 : ℝ) ^ b - 1) / 2 := by
    rw [div_le_div_iff₀ hden' (by norm_num)]
    rw [one_mul, div_mul_eq_mul_div, one_mul]
    rw [le_div_iff₀ hden]
    linarith [hstep]
  calc (hi - lo) / (2 ^ (b + 1) - 1)
      = (hi - lo) * (1 / (2 ^ (b + 1) - 1)) := by ring
    _ ≤ (hi - lo) * (1 / (2 ^ b - 1) / 2) :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
    _ = (hi - lo) / (2 ^ b - 1) / 2 := by ring

/-! ## 二、二阶矩（MSE）的一致界与零误差刻画 -/

/-- **MSE 的一致上界（与分布无关）**：在非空有限概率空间 `Ω` 上，
契约 `∀ w, |Q (x w) - x w| ≤ Δ/2` ⟹ `E[(Q x - x)²] ≤ Δ²/4`。

**它比定义多说了什么**：把**逐点契约**提升为**期望界的统一形态**，
且**对任意分布成立**。
**注意** **`Δ²/4` 不是 `Δ²/12`**：后者是均匀分布下的**精确**值，
**不是**一致上界（见文件头「边界取等检查」）。本节的界**取等可达**
（常数分布在中点）。 -/
theorem quant_mse_bound {Ω : Type*} [Fintype Ω] (Q x : Ω → ℝ) (Δ : ℝ)
    (hN : 0 < Fintype.card Ω) (hΔ : 0 < Δ)
    (hQ : ∀ w, |Q w - x w| ≤ Δ / 2) :
    (∑ w : Ω, (Q w - x w) ^ 2) / (Fintype.card Ω : ℝ) ≤ Δ ^ 2 / 4 := by
  have hNpos : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr hN
  have hterm : ∀ w : Ω, (Q w - x w) ^ 2 ≤ Δ ^ 2 / 4 := by
    intro w
    have h1 : |Q w - x w| ≤ Δ / 2 := hQ w
    calc (Q w - x w) ^ 2 = |Q w - x w| ^ 2 := by rw [sq_abs]
      _ ≤ (Δ / 2) ^ 2 := by
          exact sq_le_sq' (by linarith [abs_nonneg (Q w - x w)]) h1
      _ = Δ ^ 2 / 4 := by ring
  calc (∑ w : Ω, (Q w - x w) ^ 2) / (Fintype.card Ω : ℝ)
      ≤ (∑ _w : Ω, Δ ^ 2 / 4) / (Fintype.card Ω : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => hterm w) (le_of_lt hNpos)
    _ = Δ ^ 2 / 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_div_cancel_left₀ _ (ne_of_gt hNpos)]

/-- ⭐ **零误差的完整刻画**：`Σ_w (Q w - x w)² = 0` ⟺ `∀ w, Q w = x w`。

**它比定义多说了什么（对「何种分布最优」这一问的正名）**：
MSE 为 `0` **当且仅当**量化在**每个**样本上无失真。
- 正向：非负项之和为 `0` ⟹ 每项为 `0`（`Finset.sum_eq_zero_iff_of_nonneg`）；
- 反向：每项为 `0` ⟹ 和为 `0`。

**⟹ 结论（本文件的诚实边界）**：**不存在**「使误差最小化的非平凡分布」——
使 MSE 达 `0` 的是**无失真（量化器与数据完全匹配）**这一退化情形，
它是一个**关于量化器与数据的条件**，**不是**关于数据分布形状的最优性。
把「均匀分布最优」读作「MSE 最小」是**误读**。

**注意** 输出**不**除以 `N`（`Σ = 0 ⟺ E = 0`，因 `N > 0`），使等价性无需除零讨论。 -/
theorem quant_mse_zero_iff {Ω : Type*} [Fintype Ω] (Q x : Ω → ℝ) :
    (∑ w : Ω, (Q w - x w) ^ 2) = 0 ↔ ∀ w, Q w = x w := by
  constructor
  · intro h w
    have hw : (Q w - x w) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg (Q w - x w))).mp h w
        (Finset.mem_univ w)
    have hsub : Q w - x w = 0 := sq_eq_zero_iff.mp hw
    linarith
  · intro h
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [h w, sub_self]
    ring

end Lattice
