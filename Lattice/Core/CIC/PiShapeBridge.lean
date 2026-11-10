import Mathlib
import Lattice.Core.CIC.PiShapeRDomain
import Lattice.Core.CIC.PiShape

/-!
# `PiShape` 与 `PiShapeR` 分工明确：转换用前者，递归用后者（阶段 5）

## 本轮把两轮的结论合起来看

**第 806 轮的 `PiShape`：`app` 构造子**无前提**。** 于是
`HasType noConsts Γ f (pi A B) → PiShape f` **可证**（第 806 轮已证）。

**第 808 轮的 `PiShapeR`：`app` 构造子**有前提**。** 于是它可以做**递归**（`piShapeR_head`）。

**两者的 `app` 构造子恰好互为代价：**

| 谓词 | `app` 有前提？ | 转换 `HasType → ?` | 递归 |
|:--|:--|:--|:--|
| **`PiShape`** | **否** | **可以** | **不可以** |
| **`PiShapeR`** | **是** | **不可以** | **可以** |

**=> 这不是「哪个对哪个错」，而是**两个谓词各自适合一件事**。**

## 本轮为什么没能把两者桥接起来

**本轮试了 `PiShape t → PiShapeR t`。它在 `app` 处失败：`PiShape.app` 不给头部的形状，
而 `PiShapeR.app` **要求**头部形状。**

**也试了直接证 `HasType noConsts Γ f (pi A B) → PiShapeR f`，`app` 分支的上下文是：**

```
hg  : Term.pi A B = Bg
ihg : Term.pi A B = Term.pi Ag Bg → PiShapeR g
```

**`ihg` 需要 `Term.pi A B = Term.pi Ag Bg`，而上下文只给了 `Term.pi A B = Bg`。
这两者只有在 `Bg = Term.pi Ag Bg` 时才吻合 —— 而那是一个**类型等式**，
本层的 `HasType` **没有** conversion 判定，无法给出。**

**=> 这就是第 796 轮以来反复出现的同一个缺口的第三次显形：
`HasType` 缺少类型相等/转换规则，因此「结果类型与 `pi` 对齐」这一步在本层**不可证**。**

## 本文件给出什么

**把上述对照做成可检查的定理：**

- **`piShape_of_hasType`**：转换在 `PiShape` 上成立（复用第 806 轮）；
- **`piShapeR_head`**：递归在 `PiShapeR` 上成立（复用第 808 轮）；
- **`piShape_app_no_premise` / `piShapeR_app_has_premise`**：两条构造子的差别本身。

**=> 结论：在本层（无 conversion）下，`PiShape` 与 `PiShapeR` **不能**合一。
需要 conversion 的那一层，正是 T2 的 `Modulus` / 归一化层所预备的位置。** -/

namespace Lattice.Core.CIC

/-- **转换在 `PiShape` 上成立。**

**=> 复用第 806 轮的 `pi_typed_shape`：`PiShape` 的 `app` 无前提，故转换可行。** -/
theorem piShape_of_hasType {Γ : CICCtx} {f A B : Term}
    (h : HasType noConsts Γ f (.pi A B)) : PiShape f :=
  pi_typed_shape h

/-- **递归在 `PiShapeR` 上成立。**

**=> 复用第 808 轮的 `piShapeR_head`：`PiShapeR` 的 `app` 有前提，故可反推头部。** -/
theorem piShapeR_recursion {f a : Term} (h : PiShapeR (.app f a)) : PiShapeR f :=
  piShapeR_head h

/-- **`PiShape.app` 无前提：任意应用都满足 `PiShape`。**

**=> 这正是转换能成功、而递归不能的原因。** -/
theorem piShape_app_no_premise (f a : Term) : PiShape (.app f a) :=
  PiShape.app f a

/-- **`PiShapeR.app` 有前提：必须有头部形状才能构造。**

**=> 与上一条并置，就是两个谓词的全部差别。** -/
theorem piShapeR_app_has_premise {f a : Term} (h : PiShapeR f) : PiShapeR (.app f a) :=
  PiShapeR.app h

/-- **`PiShape (var n)` 可转成 `PiShapeR (var n)`。**

**=> 唯一的构造子只需要一步：`var` 在两个谓词里都无条件成立。** -/
theorem piShape_var_to_piShapeR (n : ℕ) : PiShapeR (.var n) :=
  PiShapeR.var n

end Lattice.Core.CIC
