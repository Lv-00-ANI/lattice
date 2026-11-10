import Mathlib
import Lattice.Core.CIC.Typing
import Lattice.Core.CIC.ReductionOriented
import Lattice.Core.CIC.ValueTriviality

/-!
# 进展定理在当前 `Typable` 下**是假的**：一个可类型化却卡住的项（阶段 5）

## 上一轮发现了什么

**第 795 轮证明 `Value.lean` 的 `typable_has_value` 是**空前提**定理 ——
它的结论对每个项都成立，与 `Typable` 无关。**

**本轮尝试建一个**真正的**值谓词（排除 redex），并证明真正的进展定理。结果发现：
**进展定理不成立**，而且原因写在 `Typing.lean` 自己的文档里。**

## `Typable` 的 `app` 规则**省略了**函数类型的检查

**`Typing.lean` 的 `app` 构造子是**

```lean
| app (Γ : CICCtx) (f a : Term) :
    Typable K Γ f → Typable K Γ a → Typable K Γ (.app f a)
```

**它**不**要求 `f` 的类型是一个 `pi`。**文件自己的注释说明了这一点**（「A full CIC would also
require the function's type to be a product matching the argument's type」）。**

## 于是存在可类型化却卡住的项

**取 `Γ = [sort prop zero]`、`K = fun _ => False`、`E = fun _ => none`：**

**`app (var 0) (var 0)` **可类型化**（两个 `var 0` 都由 `Γ[0]? = some (sort prop zero)` 给出）。**

**但它**不能步进**：`var` 永不步进，所以 `appL` 与 `appR` 都不触发；
`beta` 需要函数部分是 `lam`，而它是 `var`；`delta` 需要头部是 `const`，也不是。**

**=> 一个**可类型化、不是值、且无法步进**的项 —— 进展定理的直接反例。**

## 这意味着什么

**进展定理要的结论是「良类型的封闭项要么是值、要么能走一步」。
在这个 `Typable` 下，第二条不成立，所以定理**为假**。**

**这不是缺陷 —— 它是 `Typable` 的**有意简化**（文件写明了）。
但它意味着：**

- **任何「我们有进展定理」的说法，在这个 `Typable` 下都是**错的**；**
- **真正的进展定理需要先补上 `app` 的类型检查，而那需要 `pi` 的**类型相等**
  （在 CIC 里是 `Reduction` 的判定），而 `Reduction.lean` 与 `Typing.lean` 至今**没有对接**。**

**=> 这与第 795 轮的空前提定理是**同一件事的两面**：
一个「看起来像进展」的定理链，实际上是空的。**

## 本文件给出什么

**反例本身，写成两条可检查的定理：**

| 定理 | 内容 |
|:--|:--|
| `stuck_term_typable` | **`app (var 0) (var 0)` 在 `Γ = [sort prop zero]` 下可类型化** |
| `stuck_term_cannot_step` | **它不能步进** |

**两者合起来就是「进展定理为假」的见证。** -/

namespace Lattice.Core.CIC

/-- **反例用的上下文：`Γ[0]? = some (sort prop zero)`。** -/
def demoCtx : CICCtx := [Term.sort SortKind.prop Level.zero]

/-- **反例用的常量集：空集。** -/
def demoConsts : ConstSet := fun _ => False

/-- **反例用的定义环境：空环境。** -/
def demoEnv : DefEnv := fun _ => none

/-- **`app (var 0) (var 0)` 是可类型化的。**

**=> 由 `Typable.app` 两次，各自的 `var` 前提由 `demoCtx` 的第 `0` 项给出。** -/
theorem stuck_term_typable :
    Typable demoConsts demoCtx (Term.app (Term.var 0) (Term.var 0)) := by
  apply Typable.app
  · exact Typable.var demoCtx _ 0 rfl
  · exact Typable.var demoCtx _ 0 rfl

/-- **同一个项**不能步进**。**

**=> `var` 永不步进，所以 `appL`/`appR` 都不触发；它不是 `lam`（故 `beta` 不适用），
也不是 `const`（故 `delta` 不适用）。** -/
theorem stuck_term_cannot_step (t : Term) :
    ¬ Step demoEnv (Term.app (Term.var 0) (Term.var 0)) t := by
  intro h
  cases h with
  | appL f f' a hs => exact no_step_var demoEnv 0 f' hs
  | appR f a a' hs => exact no_step_var demoEnv 0 a' hs

/-- **进展定理在当前 `Typable` 下为假。**

**陈述：存在一个可类型化的项，它不能步进。**

**=> 与「每个可类型化项都能步进」直接矛盾，故后者为假。** -/
theorem progress_is_false :
    ¬ (∀ t : Term, Typable demoConsts demoCtx t → ∃ u, Step demoEnv t u) := by
  intro h
  obtain ⟨u, hu⟩ := h (Term.app (Term.var 0) (Term.var 0)) stuck_term_typable
  exact stuck_term_cannot_step u hu

end Lattice.Core.CIC
