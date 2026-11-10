import Mathlib
import Lattice.Core.CIC.Progress
import Lattice.Core.CIC.ReductionOriented

/-!
# 进展定理需要一个**额外前提**：常量不可用（或环境定义它们）（阶段 5）

## 本轮先做的判断，以及它给出的界限

**第 803 轮说 `app` 分支需要 `HasType K Γ f (pi A B)` 推出 `f` 的形状。本轮查证了 `f = const c`：**

```lean
HasType.const (Γ := Γ) (c := c) (A := .pi A B) (hK : K c)
```

**`const` 规则把它的**类型**作为一个**参数**，所以 `K c` 成立时，
`HasType K Γ (const c) (pi A B)` 对**任意** `A`、`B` 都成立。**

**=> 于是 `app (const c) a` 可以有自己的类型 `B`，而它**能否步进**取决于 `E c`。**

## 反例（本文件 `const_app_cannot_step`）

**取 `E = fun _ => none`（空环境）、`K = fun _ => True`、`Γ = []`：**

```
app (const c) (var 0)
```

**- **良类型化**（`HasType.app`，函数部分的类型取任意 `pi A B`）；
- **不能步进**：`appL` 需要 `const c` 走一步，而空环境下 `delta` 无前提可用；
  `appR` 需要 `var 0` 走一步，而 `no_step_var` 排除它。**

**=> 进展定理在**不加前提**时**是假的** —— 这是第 796 轮之后发现的**第二个**反例，
而且它的失败原因与第一个不同：**

| 反例 | 失败原因 |
|:--|:--|
| `app (var 0) (var 0)`（第 796 轮） | **`var 0` **自由**（`0 < Γ.length` 不成立）** |
| `app (const c) (var 0)`（本轮） | **`const c` **在空环境下不展开**（`E c = none`）** |

## 正确的进展定理需要什么

**两条中的至少一条：**

1. **`K = fun _ => False`**（没有可接受常量，于是 `HasType.const` 永不触发），或
2. **`E` 对每个 `c` 都有定义**（`∀ c, ∃ body, E c = some body`），于是 `delta` 总能触发。

**=> 这两条都是**关于环境的前提**，而不是关于项或类型的。这正是「进展定理必须携带
`DefEnv` 的性质」的精确形式。**

**本文件把反例证成定理，并把两条可选前提写下来。进展定理的完整形式是下一轮的工作，
它已经不需要新的定义，只需要选一条前提并归纳。** -/

namespace Lattice.Core.CIC

/-- **没有可接受常量的常量集。** -/
def noConsts : ConstSet := fun _ => False

/-- **对每个下标都有定义的环境。**

**=> 这是使 `delta` 总能触发的条件，也是进展定理的第二条可选前提。** -/
def TotalEnv (E : DefEnv) : Prop := ∀ c, ∃ body, E c = some body

/-- **空环境**不是**全定义环境。**

**=> 前提非平凡：`TotalEnv` 不是永远为真。** -/
theorem totalEnv_ne_empty : ¬ TotalEnv (fun _ => none) := by
  intro h
  obtain ⟨body, hb⟩ := h 0
  simp at hb

/-- **反例的构件之一：`const c` 在空环境下不能步进。**

**=> `delta` 是唯一能作用于 `const` 的构造子，而它需要 `E c = some body`。** -/
theorem const_no_step_empty (c : ℕ) (t : Term) :
    ¬ Step (fun _ => none) (.const c) t := by
  intro h
  cases h with
  | delta k body he => simp at he

/-- **本轮的核心反例：`app (const c) (var 0)` 在空环境下不能步进。**

**=> `appL` 分支由 `const_no_step_empty` 排除，`appR` 分支由 `no_step_var` 排除。
这就是「进展需要环境前提」的可检查形式。** -/
theorem const_app_cannot_step (c : ℕ) :
    ¬ ∃ u, Step (fun _ => none) (.app (.const c) (.var 0)) u := by
  rintro ⟨u, h⟩
  cases h with
  | appL f f' x hs => exact const_no_step_empty c f' hs
  | appR f x x' hs => exact no_step_var (fun _ => none) 0 x' hs

end Lattice.Core.CIC
