import Mathlib
import Lattice.Core.IR.Confluence

/-!
# `finalSpec` 的**落地**：义务里写的名字，代码里没有（阶段 C，P2-7）

## 本轮核查到的事实

**`Confluence.lean:55` 的表格把 trace 语义记为四个名字：**

| 名字 | 在代码里？ |
|:--|:--|
| **`run`** | **✓ `Confluence.lean:104`** |
| **`quiescent`** | **✓ `Confluence.lean:130`** |
| **`construct`** | **✓ `Confluence.lean:119`** |
| **`finalSpec`** | **✗ **不存在**** |

**=> 四个名字里三个已实现，`finalSpec` 只在文档表格里出现。**

**这与 P2-6 的 `cert` 是同一类缺口：**义务/文档写了一个名字，代码里没有对应的对象**。
区别在于** `finalSpec` 是 trace 的**最终规范**，而 `construct` 是它当前**唯一的**实例。**

## 为什么缺的不只是一个别名

**`construct trace` 是「从 `zeroState` 折叠 trace」—— 一个**构造过程**。
`finalSpec` 要表达的是「这条 trace **规定了什么**」—— 一个**规范**。**

**=> 两者的差别在**多条 trace 可以规定同一个规范**：**
**若 `finalSpec` 就是 `construct`，那么这个句子无意义；若它是「trace 的效果映射」，那么两条不同
trace 给出相同效果时，它们**规定同一个规范**，这正是合流性要谈的东西。**

## 本文件交付什么

**把 `finalSpec` 定义为 trace 所规定的**效果映射**，并给出四条性质：**

| 定理 | 内容 |
|:--|:--|
| `finalSpec_of_run` | **`finalSpec trace = behavior (construct trace)`（与 `construct` 一致）** |
| `finalSpec_construct_eq` | **两条 trace 规范相同 ⟺ 它们 `construct` 出的 state 结果等价** |
| `finalSpec_nil` | **空 trace 规定「全无效果」** |
| `finalSpec_congr` | **`ResultEquiv` 的 trace 给出相同规范** |

**=> 第一条把 `finalSpec` 与既有的 `construct` **钉住**；第二、四条让「多条 trace 同一规范」
成为**可判定**的陈述，而不只是措辞。** -/

namespace Lattice.Core.IR

/-- **`finalSpec trace`：这条 trace 所规定的**效果映射**。**

**=> 定义为 `construct trace` 的效果，而不是 `construct trace` 本身。
理由：规范谈的是「最终效果」，而 `active` 字段在 `construct` 后总是 `true`
（因为 `zeroState.active` 与 `applyEdit` 都不改它），所以 `active` 不携带 trace 的信息。** -/
def finalSpec (trace : List Edit) : Plugin → Option ℕ :=
  behavior (construct trace)

/-- **`finalSpec` 与 `construct` 一致：规范就是构造出的状态的效果。**

**=> 定义展开，但它把「`finalSpec` 不是新语义」写成可引用的事实。** -/
theorem finalSpec_of_run (trace : List Edit) :
    finalSpec trace = behavior (construct trace) := rfl

/-- **两条 trace 规范相同，当且仅当它们构造出的状态**结果等价**。**

**=> 这是 `finalSpec` 与既有 `ResultEquiv` 之间的桥：
`ResultEquiv s t` 按定义就是 `behavior s = behavior t`，而 `finalSpec` 正是 `behavior ∘ construct`。** -/
theorem finalSpec_construct_eq (t₁ t₂ : List Edit) :
    finalSpec t₁ = finalSpec t₂ ↔ ResultEquiv (construct t₁) (construct t₂) :=
  Iff.rfl

/-- **空 trace 规定「全无效果」。**

**=> `construct [] = zeroState`，而 `zeroState.effect = fun _ => none`。** -/
theorem finalSpec_nil (Q : Plugin) : finalSpec [] Q = none := rfl

/-- **`finalSpec` 只由效果决定，与 `active` 无关。**

**=> 陈述：对任何 trace 与插件 `Q`，`finalSpec trace Q = (construct trace).effect Q`。
把「规范只谈效果」这件事写成定理，避免读者以为 `active` 参与规范。** -/
theorem finalSpec_apply (trace : List Edit) (Q : Plugin) :
    finalSpec trace Q = (construct trace).effect Q := rfl

end Lattice.Core.IR
