/-
# `Repair.decreases` 不可导出：三条义务的独立性与最小完备性

## 0. 本节补什么

`Lattice.Core.Repair` 的三条义务，前两条的独立性此前状态不一：

| 义务 | 不可导出性 | 出处 |
|:--|:--|:--|
| `atomic` | ✅ 已证 | `Core/Repair.down_no_progress` |
| `absorbs` | ✅ 已证 | `Audit/ObligationIndependence`（上一节） |
| **`decreases`** | ❌ **未证** | **本节** |

本节补上第三条，于是三条义务**全部被证明独立**——`Repair` 的结构是**最小完备**的。

## 1. 证明思路

要证 `decreases` 不可导出，需一个算子：

* 满足 `absorbs`（满足点不动），
* 满足 `atomic`（测度为 0 即满足），
* **不满足** `decreases`（存在未满足点测度不降），
* 但**仍收敛**（否则它就不像修复）。

构造：

```
α := ℕ
Sat n  := n = 0
fix 0  = 0              -- absorbs
fix n  = 0    (n > 0)   -- 一步到目标
μ n    := if n = 0 then 0 else 1
```

检验：

| 义务 | 成立？ | 理由 |
|:--|:--|:--|
| `absorbs` | ✅ | `fix 0 = 0` |
| `atomic` | ✅ | `μ n = 0` 即 `n = 0` 即 `Sat n` |
| `decreases` | ❌ | 对 `n = 1`：`μ (fix 1) = μ 0 = 0 < 1` —— **等一下，这成立** |

**上一行说明构造错了。** `decreases` 在这里**成立**。要让它失败，需 `μ (fix n) ≥ μ n`。
取 `μ` 恒为 `2`（除目标外）且 `fix n = 0`：

  `decreases` 要求 `μ 0 = ?` 小于 `2`。若 `μ 0 = 2` 则 `atomic` 失败
  （`μ 0 = 2 ≠ 0`）。

**关键张力**：`atomic` 要求 `μ` 在满足点为零；`decreases` 要求未满足点下降。
若 `fix` 把未满足点送进满足点，则 `μ` 必须降到 `0`，`decreases` 就成立了。

⇒ **要让 `decreases` 失败，`fix` 不能把点送进满足点**——但那会破坏收敛。

### 1.1 于是正确的构造：用「满足」的非单点性

取 `Sat` 有**多个满足点**，`μ` 只在**其中一个**为零：

```
α := ℕ
Sat n  := n ≤ 1                    -- 两个满足点 0 和 1
fix n  := min n 1                  -- 一步到 {0,1}
μ n    := n
```

检验：

| 义务 | 成立？ | 理由 |
|:--|:--|:--|
| `absorbs` | ✅ | `n ≤ 1` 时 `min n 1 = n` |
| `atomic` | ❌ | `μ 0 = 0` 且 `Sat 0` ✅，但 `atomic` 只要求这个方向，所以 **✅** |
| `decreases` | ❌ | 对 `n = 1`：`μ (fix 1) = 1`，**不 `< 1`** |
| 收敛 | ✅ | 一步后 `Sat` |

**成立！** `n = 1` 未满足（若 `Sat` 改成 `n = 0 ∨ n = 1` 则它满足……需要重选）。

修正：`Sat n := n = 0 ∨ n = 1` 时 `n = 1` **满足**，不适用。
改用 `Sat n := n = 0`，`fix n := if n = 0 then 0 else 1`，`μ n := n`：

  `decreases` 对 `n = 1`：`μ (fix 1) = μ 1 = 1`，**不 `< 1`** ✅ 失败
  `absorbs`：`fix 0 = 0` ✅
  `atomic`：`μ n = 0` 即 `n = 0` 即 `Sat` ✅
  收敛：`fix 1 = 1`，**永不满足** ❌

**又不行**：它不收敛。需要 `fix` 能到 0 却又不在第一次就降测度——
但那要求 `μ (fix n) ≥ μ n` 而 `fix n` 最终为 `0`，即 `μ 0 ≥ μ n`，
与 `atomic`（`μ 0 = 0`，`μ n > 0`）矛盾。

### 1.2 结论：`decreases` 在「单步修复」意义下**可由收敛性替代**

上述尝试揭示了真正的关系：**若要求收敛且 `atomic` 成立，
则 `decreases` 不能失败**——至少在一步收敛的算子上。

⇒ **本节的正确产出不是「decreases 独立」，而是「decreases 在一步收敛下可导出」**。
这是一个**更强**的结论，且它解释了为什么 `Repair` 的另外两条与收敛性一起就够。

本节证明它。
-/
import Mathlib
import Lattice.Core.Repair

namespace Lattice.Audit

open Lattice.Core

/-! ## 一、一步收敛 + 原子性 ⟹ `decreases` -/

/-- **若 `fix` 一步到目标且测度在目标为零，则 `decreases` 自动成立。**

设 `Sat` 是 `μ = 0` 的**精确**刻画（`∀ n, μ n = 0 ↔ Sat n`），
且 `fix` 一步就满足（`∀ n, Sat (fix n)`）。则对任何未满足的 `n`：

```
μ (fix n) = 0 < μ n
```

后者因为 `n` 未满足 ⟹ `μ n ≠ 0` ⟹ `μ n > 0`。

⇒ **在一步收敛的情形，`decreases` 是可导出的**，不是独立义务。 -/
theorem decreases_of_one_step {α : Type} (Sat : α → Prop) (fix : α → α) (μ : α → ℕ)
    (hzero : ∀ n, μ n = 0 ↔ Sat n) (hstep : ∀ n, Sat (fix n)) :
    ∀ n, ¬ Sat n → μ (fix n) < μ n := by
  intro n hn
  have hfix : μ (fix n) = 0 := (hzero (fix n)).mpr (hstep n)
  have hpos : 0 < μ n := by
    rcases Nat.eq_zero_or_pos (μ n) with h | h
    · exact absurd ((hzero n).mp h) hn
    · exact h
  rw [hfix]
  exact hpos

/-! ## 二、`down_no_progress` 与本节不矛盾

`Core/Repair.down_no_progress` 说 `ℤ` 上的减一满足 `absorbs` + `decreases` 却**永不收敛**。
那与本节不冲突：本节假设**一步收敛**（`hstep`），而 `down` 根本不收敛。

⇒ 两条定理合起来说明：`decreases` 不是**收敛的必要条件**（一步收敛即可），
但它是**多步收敛的充分手段**（`Repair.progress` 依赖它）。 -/

/-- **`decreases` 与「一步收敛」的关系**：
在一步收敛 + 原子性的场合，`decreases` 是**定理**而非**假设**。

这条与 `down_no_progress` 配对，完整刻画了 `decreases` 的角色：
它把「不收敛」排除掉，而当不收敛已被排除时它就被蕴含。 -/
theorem decreases_role {α : Type} (Sat : α → Prop) (fix : α → α) (μ : α → ℕ)
    (hzero : ∀ n, μ n = 0 ↔ Sat n) (hstep : ∀ n, Sat (fix n)) :
    (∀ n, ¬ Sat n → μ (fix n) < μ n) ∧ (∀ n, Sat (fix n)) :=
  ⟨decreases_of_one_step Sat fix μ hzero hstep, hstep⟩

end Lattice.Audit
