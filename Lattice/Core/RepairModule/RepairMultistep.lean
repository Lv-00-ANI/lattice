/-
# The `Core.Repair` plugin's proofs -- MOVED from `Lattice/Core/RepairMultistep.lean`

**The DECLARATIONS do not change -- same names, same statements, same proofs, same
namespace.**
**The INTERNAL imports do: the five `Repair` files import each other, and those edges now name
the new modules so the dependency graph reports where the code actually lives.**
The old path is now a facade that imports this file and contains no proof.
-/

/-
# 多步修复算子：一把「一步不能解决」的尺子

## 0. 本节补什么，以及它化解哪两条欠账

`Lattice.Slots` 登记了两条与「修复需要几步」有关的欠账：

| 欠账 | note 原文要点 |
|:--|:--|
| `geo.loop.convergence_is_single_step` | 「迭代收敛需要一个**一步不能解决**谓词的算子」 |
| `core.repair.atomic` | 「逐算子关闭，办法是选一个在目标上为零的测度」 |

库中现有修复算子的测度值域都是 `{0, 1}`（见 `REPAIR-CENSUS.md` 的 A 类），
所以它们**一律一步到站**：既展示不了多步收敛，也展示不了 `atomic` 的必要性。

本节构造第一个测度**无界**的修复算子。

## 1. 证明思路

取 `α = ℕ`、`Sat k := k = 0`、`fix k := k - 1`、`μ k := k`。三条义务：

| 义务 | 内容 | 证明 |
|:--|:--|:--|
| `absorbs` | `k = 0 → fix k = k` | `0 - 1 = 0` |
| `decreases` | `k ≠ 0 → fix k < k` | `Nat.sub_one_lt` |
| `atomic` | `k = 0 → Sat k` | 假设本身 |

**与前 17 轮所有算子的区别**：`μ` 的值域是全体 `ℕ`，所以：

* `Repair.progress` 给出「存在某步到站」（不够强）；
* 第 17 轮的 `converges_within` 给出**恰好 `μ x = x` 步**（定量）；
* 而**任何** `n < x` 的步数都**不够**——这是本节的核心定理
  `no_uniform_bound`，它说明「一步界」对这个算子是**假**的。

## 2. 为什么这条定理重要

`geo.loop.convergence_is_single_step` 的 note 说「迭代收敛需要一个一步不能解决的算子」。
本节的 `no_uniform_bound` 就是这个算子的**证据**：

```
∀ k, 0 < k → ¬ Sat (iterate k k) ... 不，更精确地：
∀ k B, k > B → ¬ Sat (iterate B k)
```

即：**给定初始值 `k`，任何少于 `k` 步的迭代都不能让它满足**。
所以这个算子的收敛步数**不可压缩**，与 `samePointRepair` 形成对照。

## 3. 边界

- 这个算子是**人为的**（`ℕ` 上的减一）。它的价值不在于「像真实问题」，
  而在于**证明「多步收敛」这个概念在本框架内确实可实现**，
  从而让 `converges_within` 有一个非平凡实例。
- 它**不**声称任何几何约束需要多步修复。真实的几何修复算子是否多步，
  是需要逐个构造的问题（`REPAIR-CENSUS` 的 A 类共 6 个文件）。
- `atomic` 对本算子成立，因为 `Sat` 就是 `μ = 0`。本节**不**证明 `atomic`
  在别处可省——`Core/Repair.down_no_progress` 已经证明它是必要的
  （`ℤ` 上的减一满足 `absorbs` + `decreases` 却永不收敛）。
-/
import Mathlib
import Lattice.Core.RepairModule.Repair
import Lattice.Core.RepairModule.RepairConvergence
namespace Lattice.Core

namespace Multistep

/-! ## 一、算子 -/

/-- **「倒数到零」的修复算子。**

`Sat k := k = 0`，一步减一，测度就是 `k` 本身。
三条义务都平凡，但测度**无界**——这是它与库中所有既有算子（测度值域 `{0,1}`）的区别。 -/
def countdown : Repair ℕ where
  Sat := fun k => k = 0
  fix := fun k => k - 1
  μ := fun k => k
  absorbs := by
    intro k hk
    simp [hk]
  decreases := by
    intro k hk
    exact Nat.sub_one_lt (by omega)
  atomic := by
    intro k hk
    exact hk

/-! ## 二、收敛步数恰好是初始值 -/

/-- 迭代 `n` 步后是 `k - n`。 -/
theorem countdown_iterate (k n : ℕ) :
    countdown.iterate n k = k - n := by
  induction n with
  | zero => simp [Repair.iterate]
  | succ m ih =>
    rw [Repair.iterate_succ, ih]
    simp only [countdown, Nat.pred_eq_sub_one]
    omega

/-- **`n = k` 步到站**：这是第 17 轮 `converges_within` 的具体实例。 -/
theorem countdown_converges_in (k : ℕ) : countdown.Sat (countdown.iterate k k) := by
  rw [countdown_iterate]
  simp [countdown]

/-- **没有任何统一的步数界**：给定初始值 `k > 0`，任何 `n < k` 步都到不了。

这是本节的核心结论，也是 `geo.loop.convergence_is_single_step` 所要求的
「一步不能解决的算子」的**证明**。 -/
theorem no_uniform_bound (k n : ℕ) (hn : n < k) : ¬ countdown.Sat (countdown.iterate n k) := by
  rw [countdown_iterate]
  intro h
  simp only [countdown] at h
  omega

/-- **`μ` 无界**：算子取遍所有自然数，这是「一步界」不存在的原因。 -/
theorem measure_unbounded : ∀ N : ℕ, ∃ k : ℕ, N < countdown.μ k := by
  intro N
  exact ⟨N + 1, Nat.lt_succ_self N⟩

/-- **`converges_within` 在这个算子上的确切形式**：`μ k = k` 步，不多不少。 -/
theorem converges_within_is_tight (k : ℕ) :
    countdown.Sat (countdown.iterate (countdown.μ k) k)
      ∧ ∀ n : ℕ, n < countdown.μ k → ¬ countdown.Sat (countdown.iterate n k) := by
  refine ⟨countdown_converges_in k, ?_⟩
  intro n hn
  exact no_uniform_bound k n hn

end Multistep

end Lattice.Core
