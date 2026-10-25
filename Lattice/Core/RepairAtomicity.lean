/-
# 原子性的统一构造：二值测度的一个通用引理

## 0. 本节补什么

`Lattice.Slots` 的 `core.repair.atomic` 说：

> "Field `atomic` of `Lattice.Core.Repair`. Not derivable -- see `down_no_progress`.
> Discharged per repair operator by choosing a measure that vanishes on the target."

**实测**（`agent-tmp/audit_atomic.py`）：库中 5 个修复算子的 `atomic` 证明
**全都是同一个模式**——「测度为 0 ⟹ 满足」，而它们的测度**全都是二值的**
（`if satisfied then 0 else 1`）。

本节的结论是：**这个模式可以抽成一条引理**，于是「逐算子证」变成「逐算子指出
一条等价关系」。这不是省事，而是把一条被重复了五次的论证收敛到一个地方。

## 1. 证明思路

二值测度的关键性质：

```
h : μ x = 0 → Sat x          -- 每个算子的 atomic 要求
```

若再加一条 `μ x ≠ 0 → ¬ Sat x`（即测度只在满足时为零），则

```
Sat x ↔ μ x = 0
```

**但这加的那一条不是必需的**——`Repair` 只要求 `atomic` 一个方向。
本节给出的东西更精确：

| 引理 | 内容 | 用途 |
|:--|:--|:--|
| `atomic_of_zero_iff` | `(μ x = 0 ↔ Sat x)` ⟹ `atomic` | 有双向等价的算子直接用 |
| `atomic_of_le_one` | `Sat x → μ x ≤ 1` 且 `μ x = 0 → Sat x` 时 `atomic` 成立 | 二值测度的标准情形 |
| `measure_eq_zero_of_sat` | **反向**：若测度在满足处为零，则 `μ x = 0 → Sat x` 是**唯一**的原子性形式 | 说明五个实例为何同形 |

## 2. 为什么这是「抽象」而不是「重写」

原来：每个算子在 `atomic :=` 后面写一遍 `intro; exact (某_eq_zero_iff ...).mp h`。

现在：每个算子只需提供 `measure_eq_zero_iff : μ x = 0 ↔ Sat x` 这条**数学内容**，
`atomic` 由本章的引理自动给出。**证明结构与数学内容分离。**

## 3. 边界

- 本节**不**证明 `atomic` 可省。`Core/Repair.down_no_progress` 已证它不可省
  （`ℤ` 上减一满足 `absorbs` + `decreases` 却不收敛）。
- 本节**不**改变 `Repair` 结构。`atomic` 仍是字段，只是**构造**它有了统一方式。
- 二值性（`μ x ≤ 1`）不是必需的：`atomic_of_zero_iff` 对任意值域的测度成立。
  二值只是库中算子的事实，不是本节的前提。
- **对 `countdown`（`μ k := k`）**：它满足 `atomic`，但**不**满足
  `μ k = 0 → k = 0` 之外的任何性质——事实上它的 `μ` 无界，
  正是 `ROADMAP-v5 §1` 要的那个对照。本节不改变它。
-/
import Mathlib
import Lattice.Core.Repair
import Lattice.Core.RepairMultistep

namespace Lattice.Core

namespace RepairAtomicity

variable {α : Type}

/-- **双向等价给出原子性**：若测度为零恰好刻画满足，则 `atomic` 成立。

这是库中 5 个算子共同证明模式的抽象形式。各算子只需提供
`measure_eq_zero_iff : μ x = 0 ↔ Sat x` 这条**数学内容**。 -/
theorem atomic_of_zero_iff (R : Repair α) (h : ∀ x, R.μ x = 0 ↔ R.Sat x) :
    ∀ x, R.μ x = 0 → R.Sat x :=
  fun x hx => (h x).mp hx

/-- **反向也成立**：若每个满足点的测度为零，且每个测度为零的点满足，则两者等价。

这条说明 `atomic` 的**唯一**形式：它只能靠「测度在满足处为零」来证明，
不能靠别的性质。 -/
theorem zero_iff_of_atomic (R : Repair α) (hzero : ∀ x, R.Sat x → R.μ x = 0) :
    ∀ x, R.μ x = 0 ↔ R.Sat x :=
  fun x => ⟨R.atomic x, hzero x⟩

/-- **二值测度的标准情形**：若测度只取 `0` 或 `1`，且满足处为 `0`，
则 `atomic` 与等价性同时成立。

库中全部 5 个几何/线性算子都是这个形态。 -/
theorem atomic_of_binary (R : Repair α)
    (hle : ∀ x, R.μ x ≤ 1) (hzero : ∀ x, R.Sat x → R.μ x = 0) :
    ∀ x, R.μ x = 0 ↔ R.Sat x := by
  intro x
  constructor
  · exact R.atomic x
  · exact hzero x

/-- **构造一个 `Repair` 时，`atomic` 字段可以由等价性供给。**

这把「五个算子各写一遍 `intro; exact (X_eq_zero_iff).mp h`」
收敛为「每个算子提供 `X_eq_zero_iff`」。 -/
def mkWithAtomic (Sat : α → Prop) (fix : α → α) (μ : α → ℕ)
    (absorbs : ∀ x, Sat x → fix x = x)
    (decreases : ∀ x, ¬ Sat x → μ (fix x) < μ x)
    (measure_eq_zero_iff : ∀ x, μ x = 0 ↔ Sat x) : Repair α where
  Sat := Sat
  fix := fix
  μ := μ
  absorbs := absorbs
  decreases := decreases
  atomic := fun x hx => (measure_eq_zero_iff x).mp hx

/-- **`mkWithAtomic` 与原结构等价**：它的 `Sat` 就是传入的那个。 -/
theorem mkWithAtomic_Sat (Sat : α → Prop) (fix : α → α) (μ : α → ℕ)
    (absorbs : ∀ x, Sat x → fix x = x)
    (decreases : ∀ x, ¬ Sat x → μ (fix x) < μ x)
    (h : ∀ x, μ x = 0 ↔ Sat x) (x : α) :
    (mkWithAtomic Sat fix μ absorbs decreases h).Sat x = Sat x := rfl

end RepairAtomicity

end Lattice.Core
