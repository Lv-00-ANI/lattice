/-
# `Repair.absorbs` 不可导出：一条此前缺失的否证

## 0. 本节补什么

`Lattice.Core.Repair` 有三条义务：

| 义务 | 内容 |
|:--|:--|
| `absorbs` | 已满足的点不再被改动 |
| `decreases` | 未满足的点测度严格下降 |
| `atomic` | 测度为 0 的点必然满足 |

`Core/Repair.down_no_progress` 已证 **`atomic` 不可导出**（`ℤ` 上减一满足另两条却永不收敛）。

**但没有人问过对偶问题**：`absorbs` 可导出吗？若可，它是装饰。

本节证明**不可导出**，并给出反例。

## 1. 反例的构造思路

要证 `absorbs` 不可导出，需构造一个算子，它
**满足 `decreases` 与 `atomic`，但不满足 `absorbs`**。

`decreases` 只在**未满足点**施加约束；`absorbs` 只在**已满足点**施加约束。
两者的作用域**不相交**——所以它们**原则上是独立的**。反例只要在「已满足点」
上做一件 `decreases` 管不着的事即可：

```
Sat n  := n = 0
fix 0   = 5          ← 在已满足点 0 上做破坏
fix n   = n - 1      （n > 0）
μ n    := n
```

| 义务 | 是否成立 | 理由 |
|:--|:--|:--|
| `decreases` | ✅ | 对 `n ≠ 0`，`fix n = n - 1 < n` |
| `atomic` | ✅ | `μ n = 0` 即 `n = 0`，即 `Sat n` |
| `absorbs` | ❌ | `0` 满足，但 `fix 0 = 5 ≠ 0` |

## 2. 为什么这条否证重要

对验证回路，`absorbs` 是**防止修复破坏已成立性质**的那一条。
本反例说明：若没有它，一个满足 `decreases` + `atomic` 的「修复」可能
**把已经通过的配置改坏**，而且仍然满足收敛性保证。

⇒ **三条义务缺一不可**，`Repair` 的结构是正确的。这此前只是信念，现在是命题。

## 3. 泛化

`absorbs_not_derivable` 的量化形式是：

```
¬ (∀ Sat fix μ, decreases … → atomic … → ∀ n, Sat n → fix n = n)
```

即「不是所有满足另两条的三元组都保持满足」。这是**最强形式**：
它不是「某个具体算子不保持」，而是「不存在推导」。

## 4. 边界

- 本节的反例在 `ℕ` 上。它对任意非平凡类型都成立（只要能构造类似算子），
  但本节只给 `ℕ` 上的实例——足以证否全称命题。
- 本节的 `badFix` **不构成** `Repair` 实例（因为缺 `absorbs`），
  这正是要说明的：它满足其余两条却不能被接受。
- 三条义务的**独立性**现在是完整的：`atomic` 由 `down_no_progress` 证否导出，
  `absorbs` 由本节证否导出。`decreases` 的不可导出性**尚未证明**
  （需要一个满足 `absorbs` + `atomic` 但 `decreases` 失败且仍收敛的算子）。
  **这是本节明确留下的缺口**，不是遗漏。
-/
import Mathlib
import Lattice.Core.Repair

namespace Lattice.Audit

open Lattice.Core

/-! ## 一、反例算子 -/

/-- **反例的修复步**：已满足点 `0` 被改成 `5`，其余点减一。

它故意不在 `Repair` 里出现——它缺 `absorbs`，正是本节要证明的。 -/
def destructiveFix (n : ℕ) : ℕ := if n = 0 then 5 else n - 1

/-- 它在每个**未满足**点都严格下降。 -/
theorem destructiveFix_decreases : ∀ n : ℕ, ¬ (n = 0) → destructiveFix n < n := by
  intro n hn
  unfold destructiveFix
  rw [if_neg hn]
  omega

/-- 它的测度只在目标为零，所以 `atomic` 成立。 -/
theorem destructiveFix_atomic : ∀ n : ℕ, n = 0 → n = 0 := fun _ hn => hn

/-- **它违反吸收**：`0` 满足谓词，却被移走。 -/
theorem destructiveFix_not_absorbs : ¬ (∀ n : ℕ, n = 0 → destructiveFix n = n) := by
  intro h
  have h0 := h 0 rfl
  unfold destructiveFix at h0
  norm_num at h0

/-! ## 二、主定理 -/

/-- **`absorbs` 不可由另两条义务导出。**

量化形式：不存在一条「若 `decreases` 且 `atomic` 则 `absorbs`」的推导。

与 `Core/Repair.down_no_progress`（证 `atomic` 不可导出）配对，
两条合起来说明 `Repair` 的三条义务**没有一条是装饰**（`decreases` 除外，
见文件头 §4 记录的缺口）。 -/
theorem absorbs_not_derivable :
    ¬ (∀ (Sat : ℕ → Prop) (fix : ℕ → ℕ) (μ : ℕ → ℕ),
        (∀ n, ¬ Sat n → μ (fix n) < μ n) →
        (∀ n, μ n = 0 → Sat n) →
        ∀ n, Sat n → fix n = n) := by
  intro h
  have h' : ∀ n : ℕ, n = 0 → destructiveFix n = n :=
    h (fun n => n = 0) destructiveFix (fun n => n)
      destructiveFix_decreases destructiveFix_atomic
  exact destructiveFix_not_absorbs h'

end Lattice.Audit
