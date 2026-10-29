import Mathlib
import Lattice.Lib.Attention.RealAttention

/-!
# softmax 的 Lipschitz 常数：**`exp` 那一半证完了**，商那一半写清了

## 为什么这件事卡在 `exp` 上

`softmax z i = exp (z i) / ∑ j, exp (z j)`。所以它的 Lipschitz 常数由两部分决定：

1. **分子**：`exp` 在**有界区间**上的 Lipschitz 常数；
2. **分母**：`∑ exp` 随 `z` 的变化——一个**商**的估计。

**第 1 部分本轮证完**（`abs_exp_sub_le`），**第 2 部分没有做**，原因写在 §三。

## ⚠ 一个必须说清的事实：`exp` 在整个 `ℝ` 上**不是** Lipschitz 的

`|exp a − exp b| / |a − b| = exp(ξ)` 可以任意大。**所以任何「`exp` 是 L-Lipschitz」的说法都必须带上区间。**
本节的形式是**半直线** `(-∞, M]`，常数 `exp M`——这也是 softmax 里唯一有用的形式：
**softmax 的输入是分数，分数有界**。

## 与 `Block.eval_lipschitz` 的关系

`Lib/Architectures/TransformerEval` 的 `Block.eval_lipschitz` 要调用方给 `La`（注意力的 Lipschitz 常数）。
**本节给出它的 `exp` 那一半**；`La` 本身仍需要 §三 的商估计。 -/

namespace Lattice.Lib.Attention

open Lattice

/-! ## 一、`exp` 的两个不等式 -/

/-- ⭐ **`exp t − 1 ≤ t · exp t`，对全体实数 `t` 成立**（不只是 `t ≥ 0`）。

由 `Real.add_one_le_exp (−t)`：`1 − t ≤ exp (−t)`，两边乘 `exp t` 并用 `exp t · exp (−t) = 1`。 -/
theorem exp_sub_one_le (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h1 : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t)
    linarith
  have h3 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp t * (1 - t) ≤ 1 := by
    calc Real.exp t * (1 - t) ≤ Real.exp t * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos t))
      _ = 1 := h3
  nlinarith [h2]

/-- 单向：`a ≤ b ≤ M ⟹ exp b − exp a ≤ exp M · (b − a)`。 -/
theorem exp_sub_le_of_le {a b M : ℝ} (hab : a ≤ b) (hb : b ≤ M) :
    Real.exp b - Real.exp a ≤ Real.exp M * (b - a) := by
  have hb' : 0 ≤ b - a := by linarith
  have hexp : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]
    ring_nf
  have hkey : Real.exp b - Real.exp a = Real.exp a * (Real.exp (b - a) - 1) := by
    linear_combination hexp
  have hstep : Real.exp (b - a) - 1 ≤ (b - a) * Real.exp (b - a) := exp_sub_one_le _
  have h1 : Real.exp a * (Real.exp (b - a) - 1) ≤ Real.exp a * ((b - a) * Real.exp (b - a)) :=
    mul_le_mul_of_nonneg_left hstep (le_of_lt (Real.exp_pos a))
  have h2 : Real.exp a * ((b - a) * Real.exp (b - a)) = Real.exp b * (b - a) := by
    calc Real.exp a * ((b - a) * Real.exp (b - a))
        = (Real.exp a * Real.exp (b - a)) * (b - a) := by ring
      _ = Real.exp b * (b - a) := by rw [← hexp]
  rw [hkey]
  calc Real.exp a * (Real.exp (b - a) - 1)
      ≤ Real.exp a * ((b - a) * Real.exp (b - a)) := h1
    _ = Real.exp b * (b - a) := h2
    _ ≤ Real.exp M * (b - a) := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) hb'

/-- ⭐⭐ **`exp` 在 `(-∞, M]` 上是 `exp M`-Lipschitz 的**：`|exp a − exp b| ≤ exp M · |a − b|`。

**这是 softmax Lipschitz 常数的分子那一半**，而 `Block.eval_lipschitz` 的 `La` 需要它。 -/
theorem abs_exp_sub_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  rcases le_total a b with h | h
  · have h1 : |Real.exp a - Real.exp b| = Real.exp b - Real.exp a := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h))]
      ring
    have h2 : |a - b| = b - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    rw [h1, h2]
    exact exp_sub_le_of_le h hb
  · have h1 : |Real.exp a - Real.exp b| = Real.exp a - Real.exp b := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h))]
    have h2 : |a - b| = a - b := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
    rw [h1, h2]
    exact exp_sub_le_of_le h ha

/-! ## 二、softmax 的上界：它是一个概率 -/

/-- ⭐ **`softmax z i ≤ 1`**：每一项不超过总和，而总和是 1。

`softmax_nonneg` 与 `softmax_sum_one` 在 `RealAttention` 里已有，**但「≤ 1」是新的**——
三者合起来才是「`softmax z` 是一个概率分布」。 -/
theorem softmax_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (i : ι) :
    softmax z i ≤ 1 := by
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hle : softmax z i ≤ ∑ j, softmax z j :=
    Finset.single_le_sum (f := softmax z) (fun j _ => softmax_nonneg z j) hmem
  rw [softmax_sum_one z] at hle
  exact hle

/-- **三者合起来**：`softmax z` 是一个概率分布（`RealAttention.ProbDist`）。 -/
theorem softmax_probDist {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) :
    ProbDist (softmax z) :=
  ⟨softmax_nonneg z, softmax_sum_one z⟩

/-! ## 三、**没做的那一半**：商

要把 `abs_exp_sub_le` 变成 softmax 的 Lipschitz 常数，需要下面这条估计（`n` 是维数，
`a_i := exp (z i)`、`A := ∑ a`、`b_i`、`B` 同理）：

    |a_i/A − b_i/B| = |a_i·B − b_i·A| / (A·B)
                   ≤ ( |a_i − b_i|·B + b_i·|B − A| ) / (A·B)

而 `|a_i − b_i| ≤ exp M · ε`（本节的 `abs_exp_sub_le`）、`|B − A| ≤ n · exp M · ε`（求和），
**所以**：

    |softmax z i − softmax z' i| ≤ exp M · ε · (1 + n) / (n · exp m)

其中 `m` 是分数的一个下界（分母 `A ≥ n · exp m`）。

**这条没有做，理由是它需要三样本文件没有的东西**：
1. 分母的统一下界（要 `z` 的**下界**假设，否则 `exp` 可以任意小）；
2. `∑` 上 `|a_j − b_j|` 的求和估计；
3. `n` 维的 `Finset` 代数。

**它们都不是难点，是工作量。** 而**没有第 1 条时这条定理是假的**——所以先把假设写清楚，
比先写一个少了假设的版本有用。 -/

end Lattice.Lib.Attention
