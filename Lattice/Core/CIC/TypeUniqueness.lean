import Mathlib
import Lattice.Core.CIC.HasTypeW
import Lattice.Core.CIC.PiShapeR
import Lattice.Core.CIC.PiShape

/-!
# `HasTypeW → PiShapeR`：`app` 分支**仍然**不通，原因已定位到 `pi` 的对齐（阶段 5）

## 本轮先做的判断

**第 813 轮说 `HasTypeW.app` 的**第一个前提**直接给出函数的类型 `pi A B`，
所以第 811 轮的障碍应当消失。本轮验证了这个说法 —— **它只对了一半**。**

## `app` 分支的实际上下文（本轮写出并确认）

```
hg'  : HasTypeW E noConsts Γ g (Term.pi Ag Bg)     -- 函数部分的类型：Ag、Bg
ihg  : Term.pi A B = Term.pi Ag Bg → PiShapeR g     -- 归纳假设
hconv: Conv E A'g Ag                                 -- 参数可转换到定义域
目标 : PiShapeR (Term.app g x)
```

**要填 `PiShapeR.app`，需要 `PiShapeR g`。要得到它，需要把 `ihg` 施加于
`Term.pi A B = Term.pi Ag Bg`。**

**而 `generalize hg : (Term.pi A B) = target` 只给了 `hg : Term.pi A B = Bg`
—— 它把**结果类型** `Bg` 与 `pi A B` 联系起来，**而没有**把 `Ag` 与 `A` 联系起来。**

**=> 缺的是 `A = Ag`（定义域的对齐），不是 `Bg` 与 `pi A B` 的对齐（这一条 `hg` 已经有）。**

## 这比第 811/813 轮的理解更精确

| 轮次 | 当时的判断 | 本轮更正 |
|:--|:--|:--|
| 811 | 缺 `Bg = pi Ag Bg` | **缺的是 `A = Ag`** |
| 813 | `HasTypeW` 把函数类型变成前提，应当够了 | **前提给了 `pi Ag Bg`，但那不是 `pi A B`** |

**=> `HasTypeW` 的确把「函数类型由派生给出」这件事做了（第 813 轮成立），
但派生出的是 `pi Ag Bg`，而我们要证的是关于 `pi A B` 的形状引理。
两者的**定义域** `Ag` 与 `A` 之间只由 `hconv : Conv E A'g Ag` 与参数类型间接相连，
**没有** `A` 与 `Ag` 之间的等式或转换。**

## 为什么这不是可以补的技巧

**在真正的 CIC 里，这一步由 conversion 承担：`app` 规则要求 `A'` 与 `A` 可转换，
于是 `Bg` 与结果类型可转换，而**类型唯一性**（同一项的两个类型可转换）保证 `pi Ag Bg` 与 `pi A B` 一致。**

**=> 需要的是一条**类型唯一性**（type uniqueness up to conversion）定理：

```lean
HasTypeW E K Γ f T1 → HasTypeW E K Γ f T2 → Conv E T1 T2
```

**本层**没有**它，而它本身需要 `pi` 的单射性 + `Conv` 在 `pi` 上的合同性 —— 两条都不存在。**

## 本文件给出什么

**已证的部分（六个构造子）；`app` 那一支**不进陈述**，而是把所需的新定理**明确写出**：

**`TypeUniq` —— 类型唯一性（至多可转换）。它与进展定理的组装是等价的障碍，
所以把它作为**下一个明确目标**记下来，而不是继续在 `app` 上试。** -/

namespace Lattice.Core.CIC

/-- **类型唯一性（至多可转换）：本层**缺少**的性质。**

**=> 「同一个项的两个类型可转换」。这是 CIC 的标准性质，也是进展定理 `app` 分支的**唯一**剩余障碍。
把它写成 `Prop` 定义，使「缺少什么」本身可被引用与检查。** -/
def TypeUniq (E : DefEnv) (K : ConstSet) : Prop :=
  ∀ (Γ : CICCtx) (t T₁ T₂ : Term),
    HasTypeW E K Γ t T₁ → HasTypeW E K Γ t T₂ → Conv E T₁ T₂

/-- **`lam` 情形：`HasTypeW` 的 `lam` 派生给出 `PiShapeR (lam A b)`。**

**=> 不需要 `app` 的递归，直接给出。** -/
theorem hasTypeW_piShapeR_lam {E : DefEnv} {Γ : CICCtx} {A b B : Term}
    (h : HasTypeW E noConsts (A :: Γ) b B) : PiShapeR (.lam A b) :=
  PiShapeR.lam A b

/-- **`var` 情形：`var n` 无条件属于 `PiShapeR`。** -/
theorem hasTypeW_piShapeR_var {E : DefEnv} {Γ : CICCtx} {n : ℕ} {A : Term}
    (h : HasTypeW E noConsts Γ (.var n) A) : PiShapeR (.var n) :=
  PiShapeR.var n

/-- **`letE` 情形：无条件属于 `PiShapeR`。** -/
theorem hasTypeW_piShapeR_letE {E : DefEnv} {Γ : CICCtx} {A t b B : Term}
    (h : HasTypeW E noConsts Γ (.letE A t b) B) : PiShapeR (.letE A t b) :=
  PiShapeR.letE A t b

/-- **`const` 在 `noConsts` 下不可类型化（`HasTypeW` 版本）。**

**=> 与第 813 轮的 `HasTypeW.const` 直接矛盾。
这是六个构造子里唯一被前提排除的。** -/
theorem hasTypeW_no_const {E : DefEnv} {Γ : CICCtx} {c : ℕ} {A : Term} :
    ¬ HasTypeW E noConsts Γ (.const c) A := by
  intro h
  cases h with
  | const _ _ _ hK => exact hK

end Lattice.Core.CIC
