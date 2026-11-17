import Mathlib
import Lattice.Lib.Compiler.PiecewiseWeights
import Lattice.Lib.Compiler.NonlinearApproximation

/-!
# 分段线性族的**一致**逼近（阶段 E，P8）

## 本文件是误差界的**唯一权威**

**第 955 轮的界只对 `x < 1` 成立，因为 `segmentIndex n 1 = n` 越界，
而 `WeightSequence.piecewiseFamily_error` 要求 `k < n`。**

**=> 但端点上函数值**恰好精确**（`piecewiseWeights n 1 = 1 = 1²`），只是那条路径覆盖不到。**

**第 959 轮：**

1. **补上端点 `x = 1`（误差为 `0`）；**
2. **把界提升为**闭区间** `[0,1]` 上的界——这是本库关于该族的**唯一**误差界定理
   （半开区间版本已删除，见 `PiecewiseWeights` 的 docstring）；**
3. **给出**一致**逼近：`∀ ε > 0, ∃ n ≥ 1, ∀ x ∈ [0,1], |x² - ws n x| ≤ ε`。**

## 为什么第 3 条重要

**第 951 轮的 R2 是「存在一列界趋于零」——**逐点/序列**形式。**
**=> 第 3 条是**一致**形式：`∀ ε ∃ n ∀ x`，这正是审计表格里 R1 的形状。**

**=> 而 R1 对**线性族**为假（第 944 轮 `1/8` 地板），
对**分段线性族**为真，且**一致**为真。**

**=> 所以「目标被设成数学上不成立的形式」的精确说法应当是：
**作用域被设得太宽（含线性族）**，而不是「形式本身不可满足」。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`segmentIndex_at_one`** | **⭐ `segmentIndex n 1 = n`** |
| **`piecewiseWeights_at_one`** | **⭐⭐ `piecewiseWeights n 1 = 1`** |
| **`piecewiseWeights_error_at_one`** | **⭐ 端点误差为 `0`** |
| **`piecewiseWeights_error_closed`** | **⭐⭐⭐ 闭区间 `[0,1]` 上的界（唯一权威）** |
| **`piecewiseWeights_uniform_tendsto`** | **⭐⭐⭐ `∀ ε > 0, ∃ n ≥ 1, ∀ x ∈ [0,1], 误差 ≤ ε`** | -/

namespace Lattice.Lib.Compiler.PiecewiseUniform

open Set Filter Topology
open Lattice.Lib.Compiler.PiecewiseWeights

/-- **⭐ `segmentIndex n 1 = n`。**

**=> `⌊n·1⌋ = ⌊n⌋ = n`（`n` 为自然数，其强制转换是整数）。** -/
theorem segmentIndex_at_one (n : ℕ) : segmentIndex n 1 = n := by
  unfold segmentIndex
  rw [mul_one]
  exact Nat.floor_natCast n

/-- **⭐⭐ `piecewiseWeights n 1 = 1`。**

**=> 在 `x = 1` 处，`segmentIndex = n`，割线段为 `[n/n, (n+1)/n] = [1, 1+1/n]`，
而该割线在 `x = 1` 处的值恰为 `1`。**

**=> 所以端点是**精确**的，误差为 `0`。** -/
theorem piecewiseWeights_at_one (n : ℕ) (hn : 0 < n) : piecewiseWeights n 1 = 1 := by
  unfold piecewiseWeights
  rw [segmentIndex_at_one]
  rw [Lattice.Lib.Compiler.WeightSequence.chordSegment_eval]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **⭐ 端点处的界：误差为 `0`，故不超过 `(1/n)²/4`。** -/
theorem piecewiseWeights_error_at_one (n : ℕ) (hn : 0 < n) :
    |(1 : ℝ) ^ 2 - piecewiseWeights n 1| ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  rw [piecewiseWeights_at_one n hn]
  norm_num
  positivity

/-- **⭐⭐⭐ **闭区间** `[0,1]` 上的误差界（本库唯一权威）。**

**=> 内部由 `WeightSequence.piecewiseFamily_error` 给出，
端点 `x = 1` 由 `piecewiseWeights_error_at_one` 给出（误差恰为 `0`）。** -/
theorem piecewiseWeights_error_closed (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |x ^ 2 - piecewiseWeights n x| ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  rcases eq_or_lt_of_le hx.2 with hone | hlt
  · -- the right endpoint, handled exactly (`subst`, not `rw`, so the divisor is untouched)
    subst hone
    exact piecewiseWeights_error_at_one n hn
  · -- the interior: locate the piece, then apply the chord bound
    have hk : segmentIndex n x < n := segmentIndex_lt n hn x hx.1 hlt
    have hmem := segmentIndex_mem n x hx.1
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hxI : x ∈ Icc (((segmentIndex n x : ℝ)) / n) ((((segmentIndex n x : ℝ)) + 1) / n) := by
      constructor
      · show ((segmentIndex n x : ℝ)) / n ≤ x
        rw [div_le_iff₀ hn']; linarith [hmem.1]
      · show x ≤ (((segmentIndex n x : ℝ)) + 1) / n
        rw [le_div_iff₀ hn']; linarith [hmem.2]
    have hb := Lattice.Lib.Compiler.WeightSequence.piecewiseFamily_error
      n hn (segmentIndex n x) hk x hxI
    unfold piecewiseWeights
    exact hb

/-- **⭐⭐⭐ 一致逼近：`∀ ε > 0`，存在 `n ≥ 1`，使 `[0,1]` 上**处处**误差 `≤ ε`。**

**=> 这是 R1 的**一致**形式，而它在**分段线性族**上成立。**

**=> 证明：取 `quarter_inv_sq_tends_to_zero`（第 949 轮）给出的 `n`，
再用 `piecewiseWeights_error_closed`。** -/
theorem piecewiseWeights_uniform_tendsto :
    ∀ ε > 0, ∃ n : ℕ, 1 ≤ n ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |x ^ 2 - piecewiseWeights n x| ≤ ε := by
  intro ε hε
  obtain ⟨n, hn1, hn⟩ :=
    Lattice.Lib.Compiler.NonlinearApproximation.quarter_inv_sq_tends_to_zero ε hε
  refine ⟨n, hn1, fun x hx => ?_⟩
  refine le_trans (piecewiseWeights_error_closed n (by omega) x hx) ?_
  -- (1/n)^2/4 = 1/(4n^2)
  have heq : (1 / (n : ℝ)) ^ 2 / 4 = 1 / (4 * (n : ℝ) ^ 2) := by
    field_simp
    ring
  rw [heq]
  exact hn

end Lattice.Lib.Compiler.PiecewiseUniform
