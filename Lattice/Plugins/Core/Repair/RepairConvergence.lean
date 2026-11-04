/-
# The `Core.Repair` plugin's proofs -- MOVED from `Lattice/Core/RepairConvergence.lean`

**The DECLARATIONS do not change -- same names, same statements, same proofs, same
namespace.**
**The INTERNAL imports do: the five `Repair` files import each other, and those edges now name
the new modules so the dependency graph reports where the code actually lives.**
The old path is now a facade that imports this file and contains no proof.
-/

/-
# 修复回路的收敛率：步数由测度给出

## 0. 本节补上什么

`Lattice.Core.Repair.progress` 证明的是**存在性**：

```
∀ x, ∃ n, Sat (iterate n x)
```

它没有给出 `n` 的界。`PROOF-CHAIN-RUNG.md` 与 `STATE-2026-10.md` 都把「收敛率缺失」
列为闭环的最后一块。本节补上：**`n = μ x` 步之内必然满足**。

## 1. 证明思路

`Repair` 的三条公理是：

| 公理 | 内容 |
|:--|:--|
| `absorbs` | 已满足的点不再变化 |
| `decreases` | 未满足的点测度严格下降 |
| `atomic` | 测度为 `0` 的点必然满足 |

于是对任意 `n`：

```
若前 n 步都未满足，则 μ(iterate n x) + n ≤ μ x
```

**归纳**：`n = 0` 时是 `μ x ≤ μ x`；每一步 `decreases` 给出 `μ` 至少降 `1`。

取 `n = μ x`：若仍未满足，则 `μ(iterate (μ x) x) + μ x ≤ μ x`，
即 `μ(iterate (μ x) x) ≤ 0`，故 `= 0`，由 `atomic` 得 `Sat`。矛盾。

**所以 `Sat (iterate (μ x) x)` 成立**——这是精确的界，不是估计。

## 2. 为什么这是「收敛率」而不是「收敛性」

| 论断 | 强度 |
|:--|:--|
| `progress`：`∃ n, Sat (iterate n x)` | 收敛性（无论多久） |
| **`converges_within`：`Sat (iterate (μ x) x)`** | **收敛率**（步数有界，界可计算） |

界的意义：`μ x` 是**可计算的自然数**，不是抽象的「某个 n」。
对具体修复算子（如 `Geo.Loop.fixSamePoint`），`μ x` 是 `0` 或 `1`，
所以界就是「一步」。这解释了 `loop_converges_in_one` 为什么成立——
它是本定理的一个实例。

## 3. 泛化

本定理对**任意** `Repair α` 成立，不依赖 `α` 的结构。
它是 `Repair` 三条公理的直接推论，所以：
- 对 `Repair`（`μ : α → ℕ`）成立；
- `RepairWF`（任意良基序）的版本需要「良基序上的深度」，
  那不是自然数，无法写出显式界——**这正是两者的区别**。

## 4. 边界

- 界 `μ x` 是**上界**，不是最小值。真实步数可能更少：若 `fix` 一次降很多，
  实际步数小于 `μ x`。给出精确步数需要知道每步的降幅，是更强的前提。
- `μ : α → ℕ` 不可省：`RepairWF` 允许任意良基序，那里没有「步数界」这种陈述
  （良基序可以有无穷长的下降链，例如 `ω`）。
- 本定理**不**给出「每一步都进展」的定量形式（如「每步降 `c > 0`」）；
  那是 `decreases` 已经隐含的，但把它写成数值需要在结构里加字段。
-/
import Mathlib
import Lattice.Plugins.Core.Repair.Repair

namespace Lattice.Core

namespace RepairConvergence

variable {α : Type}

/-- **收敛率：`μ x` 步之内必然满足。**

这是 `progress` 的定量形式。证明用归纳得出「若前 `n` 步都失败，则测度至少降 `n`」，
再取 `n = μ x`，由 `atomic` 得到矛盾。 -/
theorem converges_within (R : Repair α) (x : α) :
    R.Sat (R.iterate (R.μ x) x) := by
  -- Key invariant: after n steps, either it passes, or μ has dropped by at least n.
  have key : ∀ n : Nat, R.Sat (R.iterate n x) ∨ R.μ (R.iterate n x) + n ≤ R.μ x := by
    intro n
    induction n with
    | zero =>
      right
      simp only [Repair.iterate]
      exact le_rfl
    | succ k ih =>
      rcases ih with hpass | hbound
      · -- already passing: absorption keeps it passing
        left
        rw [Repair.iterate_succ, R.absorbs _ hpass]
        exact hpass
      · by_cases hk : R.Sat (R.iterate k x)
        · left
          rw [Repair.iterate_succ, R.absorbs _ hk]
          exact hk
        · -- still failing: decrease by at least one
          right
          have hdec : R.μ (R.fix (R.iterate k x)) < R.μ (R.iterate k x) :=
            R.decreases _ hk
          rw [Repair.iterate_succ]
          omega
  rcases key (R.μ x) with hpass | hbound
  · exact hpass
  · -- μ (iterate (μ x) x) + μ x ≤ μ x  forces  μ = 0
    have hzero : R.μ (R.iterate (R.μ x) x) = 0 := by omega
    exact R.atomic _ hzero

/-- **步数界是可计算的**：`μ x` 是自然数。

这条定理把「界存在」变成「界是一个具体的自然数」，使其可以逐例计算。 -/
theorem converges_within_steps (R : Repair α) (x : α) :
    ∃ n : Nat, n = R.μ x ∧ R.Sat (R.iterate n x) :=
  ⟨R.μ x, rfl, converges_within R x⟩

/-- **`progress` 由收敛率直接得到。**

`progress` 的存在性陈述是本定理与 `⟨μ x, ·⟩` 的组合，并非独立的事实。 -/
theorem progress_of_rate (R : Repair α) (x : α) :
    ∃ n : Nat, R.Sat (R.iterate n x) :=
  ⟨R.μ x, converges_within R x⟩

end RepairConvergence

end Lattice.Core
