import Mathlib
import Lattice.Lib.Compiler.WeightSequence

/-!
# 权重序列的**单一函数**打包（阶段 C，P8）

## 关闭第 954 轮 §10 的第 4 项

**§10 原文：**

> **R2 的权重序列被包成单一 `ℕ → Weights` 函数**——`WeightSequence` 给出逐片的
> `Segment` 与界，未声明整族是单一函数。

**=> 本文件把它包成单一函数。**
**=> 分段索引用 `Nat.floor (n·x)`，其形态经 `Lattice/Probe/PieceIndex.lean` 试验确定后移入此处。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`pieceOf`** | **⭐⭐ 分段索引 `k = ⌊n·x⌋₊`** |
| **`segmentIndex_lt`** | **⭐ `x < 1` 时 `k < n`** |
| **`segmentIndex_mem`** | **⭐⭐ `x` 落在第 `k` 段的交叉相乘形式** |
| **`piecewiseWeights`** | **⭐⭐⭐ 单一函数 `ws : ℕ → ℝ → ℝ`（`n` 段分段线性）** |
| **`piecewiseWeights_error`** | **⭐⭐⭐ 该函数的误差 `≤ (1/n)²/4`（`x < 1` 时）** | -/

namespace Lattice.Lib.Compiler.PiecewiseWeights

open Set

/-- **⭐⭐ 分段索引 `k = ⌊n·x⌋₊`。** -/
noncomputable def segmentIndex (n : ℕ) (x : ℝ) : ℕ := Nat.floor ((n : ℝ) * x)

/-- **⭐ `x < 1` 时 `segmentIndex n x < n`。** -/
theorem segmentIndex_lt (n : ℕ) (hn : 0 < n) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    segmentIndex n x < n := by
  unfold segmentIndex
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) * x := mul_nonneg (le_of_lt hn') hx0
  have hle : ((Nat.floor ((n : ℝ) * x) : ℝ)) ≤ (n : ℝ) * x := Nat.floor_le hnonneg
  have hlt : (n : ℝ) * x < (n : ℝ) * 1 := by nlinarith
  have hfloor : ((Nat.floor ((n : ℝ) * x) : ℝ)) < (n : ℝ) := by linarith
  exact_mod_cast hfloor

/-- **⭐⭐ `x` 落在第 `segmentIndex n x` 段内（交叉相乘形式）。**

**=> `k ≤ x·n` 且 `x·n < k+1`。** -/
theorem segmentIndex_mem (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) :
    ((segmentIndex n x : ℝ)) ≤ x * (n : ℝ) ∧ x * (n : ℝ) < ((segmentIndex n x : ℝ)) + 1 := by
  unfold segmentIndex
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) * x := by
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    exact mul_nonneg this hx0
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((n : ℝ) * x)
  constructor <;> linarith

/-- **⭐⭐⭐ 单一函数：`n` 段分段线性权重。**

**=> `ws n x` 取 `x` 所在段的割线值。
在 `x ∈ [0,1)` 上这是 `n` 段分段线性函数，全部由 `pieceOf` 决定。** -/
noncomputable def piecewiseWeights (n : ℕ) (x : ℝ) : ℝ :=
  (Lattice.Lib.Compiler.WeightSequence.chordSegment
    ((segmentIndex n x : ℝ) / n) (((segmentIndex n x : ℝ) + 1) / n)).eval x

/-- **⭐⭐⭐ 该单一函数的误差 `≤ (1/n)²/4`。**

**=> 在 `x ∈ [0,1)` 上，`piecewiseWeights n x` 正是第 `k` 段的割线，
故由 `WeightSequence.piecewiseFamily_error` 直接给出误差界。**

**=> 这就是 §10 第 4 项的闭合：**权重族现在是**单一函数** `ℕ → ℝ → ℝ`，
而不再只是逐片 `Segment` 的集合。** -/
theorem piecewiseWeights_error (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |x ^ 2 - piecewiseWeights n x| ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  have hk : segmentIndex n x < n := segmentIndex_lt n hn x hx0 hx1
  -- the cross-multiplied membership, converted to the [k/n, (k+1)/n] form
  have hmem := segmentIndex_mem n x hx0
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hxI : x ∈ Icc (((segmentIndex n x : ℝ)) / n) ((((segmentIndex n x : ℝ)) + 1) / n) := by
    constructor
    · show ((segmentIndex n x : ℝ)) / n ≤ x
      rw [div_le_iff₀ hn']; linarith [hmem.1]
    · show x ≤ (((segmentIndex n x : ℝ)) + 1) / n
      rw [le_div_iff₀ hn']; linarith [hmem.2]
  have hb := Lattice.Lib.Compiler.WeightSequence.piecewiseFamily_error
    n hn (segmentIndex n x) hk x hxI
  -- the packed function IS the chord segment, so the bound applies directly
  unfold piecewiseWeights
  exact hb

end Lattice.Lib.Compiler.PiecewiseWeights
