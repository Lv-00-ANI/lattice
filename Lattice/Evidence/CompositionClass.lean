/-
# 组合判定：把「需要什么」编码进类型

## 0. 本节补什么

`PROOF-CHAIN-RUNG §5.5` 登记了三类组合与三种代价，`ROADMAP-v11 §2.1` 的第一优先是：

> 给一个组合判定器——输入两个条款的载体签名，输出「需要什么」。
> **一条消除判断的定理，胜于十条增加案例的定理。**

本节实现那个判定器的正确形态。

## 1. 两次失败的尝试，以及它们各自说明了什么

**尝试一**：用 `if P = Q then sequential else bridged` 自动判定。
**失败原因**：`Prop` 的命题相等不是「同一性质」该有的意思，而且 `Decidable`/`if` 的展开
污染了每条下游证明。**这是一个信号：判定不该在项层面做。**

**尝试二**：写一条统一的 `compose_by_kind` 返回 `Q (g (f x))`。
**失败原因**：`sequential` 分支的结论**应当是** `P (g (f x))`，不是 `Q (…)`。
**类型检查器拒绝了它**——这恰恰说明两类的**结论形状不同**。

## 2. 正确的形态：判定的产物是「证据类型 × 结论类型」

| 类 | 证据 | 结论 |
|:--|:--|:--|
| `sequential` | **无** | `P (g (f x))` |
| `bridged` | `∀ x, P x → Q x` | `Q (g (f x))` |

**所以「需要什么」不是一个值，而是一对类型。** 下面把它编码成 `Signature`。

**判定器因此是类型族，不是函数**：调用者选 `k`，`Signature k P Q` 就决定了
证据与结论的形状。**选错 `k` 会构造不出证据——错误在编译期，不在评审时。**

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `CompositionKind` | `sequential` / `bridged` |
| `Evidence` | 按 `k` 决定的证据类型 |
| `Signature` | 按 `k` 决定的（证据，结论）对 |
| `compose_sequential` | 同性质：**无需额外证据** |
| `compose_bridged` | 换性质：**消耗一条桥** |
| `signature_sequential` / `signature_bridged` | 两个签名都是 `rfl` |
| `bridged_needs_bridge` | 桥是**必要**条件，不是保守估计 |

## 4. 边界

- 本节只判定**顺序**组合。并置组合（`Lift.ChainComposition.CompatiblePair`）不在此枚举内：
  它的代价是**两个结构之间的等式** `agrees`，形状与「阶段之间的蕴含」不同。
- 判定**不移除证明义务**：它说「你需要一座桥」，桥本身仍要人给。
  **减少的是「该用哪条定理」的判断，不是「证明蕴含」的工作。**
- 本节**不**覆盖「三个以上阶段混合两种类」的情形。那需要 `List CompositionKind` 与
  逐段桥，是可以做的推广，但不在本轮范围。
-/
import Mathlib
import Lattice.Evidence.BridgedComposition

namespace Lattice.Audit

namespace CompositionClass

/-! ## 一、判定结果与证据 -/

/-- **一次组合属于哪一类。** -/
inductive CompositionKind where
  /-- 所有阶段保持**同一**性质。 -/
  | sequential
  /-- 阶段之间**换了**性质。 -/
  | bridged
  deriving DecidableEq, Repr

/-- **按判定结果需要提供的证据。**

`sequential` 是 `True`——**这说明它确实不需要额外东西**，而不是文档里那么一说。
`bridged` 是一条蕴含。 -/
def Evidence {α : Type} : CompositionKind → (α → Prop) → (α → Prop) → Prop
  | .sequential, _, _ => True
  | .bridged, P, Q => ∀ x, P x → Q x

/-- **按判定结果决定的（证据类型，结论类型）对。**

这是本节的核心：**「需要什么」是一对类型，不是一个值。** -/
def Signature {α : Type} (k : CompositionKind) (P Q : α → Prop) : Prop × (α → Prop) :=
  match k with
  | .sequential => (True, P)
  | .bridged => (∀ x, P x → Q x, Q)

/-! ## 二、两类各自的组合定理 -/

/-- **`sequential`：同性质，结论仍是该性质，无需任何额外证据。** -/
theorem compose_sequential {α : Type} (P : α → Prop) (f g : α → α)
    (hf : ∀ x, P x → P (f x)) (hg : ∀ x, P x → P (g x))
    (x : α) (hx : P x) :
    P (g (f x)) :=
  hg (f x) (hf x hx)

/-- **`bridged`：换性质，结论是目标性质，代价是一条桥。** -/
theorem compose_bridged {α : Type} (P Q : α → Prop) (f g : α → α)
    (hf : ∀ x, P x → P (f x)) (hg : ∀ x, Q x → Q (g x))
    (ev : Evidence .bridged P Q)
    (x : α) (hx : P x) :
    Q (g (f x)) :=
  hg (f x) (ev (f x) (hf x hx))

/-! ## 三、签名的可计算性 -/

/-- **`sequential` 的签名**：证据 `True`，结论 `P`。 -/
theorem signature_sequential {α : Type} (P Q : α → Prop) :
    Signature .sequential P Q = (True, P) := rfl

/-- **`bridged` 的签名**：证据是桥，结论是 `Q`。 -/
theorem signature_bridged {α : Type} (P Q : α → Prop) :
    Signature .bridged P Q = (∀ x, P x → Q x, Q) := rfl

end CompositionClass

end Lattice.Audit
