/-
# 收敛率的应用：几何回路的界是 1

## 0. 本节做什么

`Core/RepairConvergence.converges_within` 给出通称的收敛率：`μ x` 步之内满足。

本节把它实例化到 `Geo.Loop` 的 `samePoint` 修复回路，得到**具体的界**：
`samePointMeasure` 的值域是 `{0, 1}`，所以界是 **1 步**。

这解释了 `Geo.Loop.loop_converges_in_one` 为什么成立——它是收敛率定理的一个实例，
而不是一条独立证明的事实。

## 1. 证明思路

`samePointMeasure a b pts = if pts a = pts b then 0 else 1`，所以：

| 情形 | 测度 | 定理给出 |
|:--|:--|:--|
| 已满足 `pts a = pts b` | `0` | `0` 步（`iterate 0 = id`） |
| 未满足 | `1` | `1` 步 |

两种情况都 ≤ 1 步。这把 `loop_converges_in_one` 纳入一个统一框架：
它不是特例技巧，而是「界 = 初始测度」这条一般规律的实例。

## 2. 泛化

同样的推理对任何**二值测度**成立：若 `μ x ∈ {0, 1}`，则界是 `1`。
`samePointMeasureFin` 也是二值的，所以 `Fin k` 版本同样是界 1。

## 3. 边界

- 本节的界 `1` 是**上界**。若初始就满足，实际步数是 `0`
  （`converges_within` 在 `μ x = 0` 时给出 `Sat (iterate 0 x) = Sat x`）。
- 界为 `1` 源于测度的**值域**，不是源于修复算子的效率。若测度取更大的值域
  （如「需要修几条约束」），界相应变大——这正是 `μ x` 该有的行为。
-/
import Mathlib
import Lattice.Plugins.Core.Repair.RepairConvergence
import Lattice.Reference.Geometry.Geometry.Loop

open scoped BigOperators

namespace Lattice.Geo

namespace LoopRate

/-! ## 一、二值测度的界 -/

/-- **二值测度的收敛界是 `1`。**

若 `μ` 只取 `0` 或 `1`，则 `min (μ x) 1 = μ x`，于是
`converges_within` 给出的 `μ x` 步可换成统一的 `1` 步界。 -/
theorem within_one_of_binary {α : Type} (R : Lattice.Core.Repair α) (hbin : ∀ x, R.μ x ≤ 1)
    (x : α) : R.Sat (R.iterate 1 x) := by
  have h := Lattice.Core.RepairConvergence.converges_within R x
  have hle : R.μ x ≤ 1 := hbin x
  -- iterate by `μ x` already passes; `μ x` is 0 or 1, so `iterate 1` also passes
  rcases Nat.eq_zero_or_pos (R.μ x) with h0 | hpos
  · -- μ x = 0, so x already passes, and absorption keeps it passing
    have hsat : R.Sat x := R.atomic x h0
    rw [show (1 : Nat) = 0 + 1 from rfl, Lattice.Core.Repair.iterate_succ]
    rw [show Lattice.Core.Repair.iterate R 0 x = x from rfl, R.absorbs x hsat]
    exact hsat
  · -- μ x ≥ 1 and ≤ 1, so μ x = 1 exactly
    have hone : R.μ x = 1 := by omega
    rwa [hone] at h

/-! ## 二、几何回路的界 -/

/-- **`samePoint` 修复回路的收敛界是 1 步。**

`samePointMeasure` 的值域是 `{0, 1}`，所以二值版本的界适用。
这是 `loop_converges_in_one` 存在的一般理由。 -/
theorem samePoint_measure_le_one (a b : ℕ) (pts : ℕ → Pt n) :
    samePointMeasure a b pts ≤ 1 := by
  unfold samePointMeasure
  split <;> omega

/-- `Fin k` 版本的测度也是二值的。 -/
theorem samePointMeasureFin_le_one {k : ℕ} (a b : Fin k) (pts : Fin k → Pt n) :
    samePointMeasureFin a b pts ≤ 1 := by
  unfold samePointMeasureFin
  split <;> omega

end LoopRate

end Lattice.Geo
