/-
# 多段组合：类型强制衔接

## 0. 本节补什么

`Audit/CompositionClass.lean`（第 59 轮）把**两段**组合的判定编码进类型。
`ROADMAP-v11 §4` 登记了它未覆盖的情形：「三个以上阶段混合两种类」。**本节做那个推广。**

## 1. 两次失败的写法，以及它们各自暴露的问题

**写法一**：两个平行列表（判定列表 + 性质列表），按索引对应。
**问题**：索引地狱——每条定理都要同时说「第 `i` 个性质」与「第 `i` 个判定」，证明不可读。

**写法二**：`inductive Step | same (P) | change (P Q) (h : ∀ x, P x → Q x)`，
再沿列表折叠。
**问题**：**列表里两步之间没有任何约束**。`[change P Q h, same R]` 是合法项，
可它的出口性质是 `R`，与 `Q` 无关——**「衔接」没有被类型表达**。
（我写这条时，`compose_steps` 的签名不得不引入 `head?.map` 之类的东西来回避这一点，
而那不是证明，是把缺陷藏进签名。）

## 2. 正确形态：用「依赖对」强制衔接

衔接的正确表达是**存在依赖**：第二步的入口**就是**第一步的出口。用 `Sigma`：

```
structure Link (P : α → Prop) where
  Q : α → Prop
  h : ∀ x, P x → Q x
```

`Link P` 的**类型参数**是入口性质 `P`，出口 `Q` 是字段。
于是「下一步的入口」由**前一链的 `Q`** 给出——**衔接是类型，不是约定**。

**多段组合就是一个从首性质出发的链**：

```
inductive Chain : (α → Prop) → Type
  | nil (P)
  | cons {P} (Q) (h : ∀ x, P x → Q x) (rest : Chain Q)
```

**`rest : Chain Q`** 这一项就是衔接：它要求下一段的入口恰是 `Q`。
⇒ `[change P Q h, same R]` **根本构造不出来**。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `Chain` | 从某性质出发的链，**构造子强制衔接** |
| `Chain.out` | 链的出口性质 |
| `Chain.length` | 段数 |
| `compose_chain` | **多段组合**：`P x` ⟹ 链出口在 `x` 处成立 |
| `chain_nil` / `chain_cons` | 与两段版本对照 |
| `no_skip_possible` | **无法跳过中间性质**：链的构造子只允许相邻转手 |

## 4. 为什么这不只是两段版本加长

第 59 轮的 `sequential`/`bridged` 是**外部判定**，与性质**分离**：误标能被抓到，
但判据和数据是两件东西。

本节的 `Chain` 让**衔接成为类型下标**：不存在「判定说接上了、实际没接」的状态。
⇒ **判据与数据同行**，这比「判据在旁边」更难出错。

## 5. 边界

- 仍是**顺序**组合。并置（`ChainComposition.CompatiblePair`）不在此列。
- **不自动推断**链：使用者构造它，类型检查它。自动推断需把「性质是否相等」变可判定，
  而第 59 轮已论证**命题相等不是正确判据**。
- 桥是**相邻**的。非相邻桥需复合，本节不自动合成：
  第 47 轮 `bridge_is_necessary` 已证传递性对换性质的情形**不成立**。
- 不处理「同一阶段重复」（闭环迭代）：那是 `Nat.iterate` 形状，由
  `ChainTransitivity.preserves_iterate` 负责。
- `Chain` 与第 46 轮的 `preserves_foldl` **不重叠**：后者要求**同一性质**贯穿全部阶段，
  本节允许性质逐步改变。
-/
import Mathlib
import Lattice.Audit.CompositionClass

namespace Lattice.Audit

namespace MultiComposition

open CompositionClass

variable {α : Type}

/-! ## 一、链：衔接由类型强制 -/

/-- **从性质 `P` 出发的组合链。**

`cons` 的 `rest` 项类型是 `Chain Q`，而 `Q` 正是 `h` 的**目标**——
⇒ **下一段的入口被强制等于这一段的出口**。`[change P Q, same R]`（`R ≠ Q`）构造不出来。 -/
inductive Chain (α : Type) : (α → Prop) → Type _ where
  /-- 空链：性质不变。 -/
  | nil (P : α → Prop) : Chain α P
  /-- 一段：从 `P` 转到 `Q`，其余部分必须从 `Q` 继续。 -/
  | cons {P : α → Prop} (Q : α → Prop) (h : ∀ x, P x → Q x) (rest : Chain α Q) :
      Chain α P

/-- **链的出口性质。** -/
def Chain.out : {P : α → Prop} → Chain α P → (α → Prop)
  | _, .nil P => P
  | _, .cons Q _ rest => rest.out

/-- **段数。** -/
def Chain.length : {P : α → Prop} → Chain α P → ℕ
  | _, .nil _ => 0
  | _, .cons _ _ rest => rest.length + 1

/-! ## 二、多段组合 -/

/-- **多段组合：`P x` ⟹ 链出口在 `x` 处成立。**

每一段用它自己的桥把性质送过去；`nil` 是恒等。
**这是第 59 轮两条两段定理的链形式。** -/
theorem compose_chain : ∀ {P : α → Prop} (c : Chain α P) (x : α), P x → c.out x
  | _, .nil _, _, hx => hx
  | _, .cons _ h rest, x, hx => compose_chain rest x (h x hx)

/-! ## 三、与两段版本的对照 -/

/-- **一段的链就是一次两段组合**（第 59 轮的 `compose_bridged`）。 -/
theorem chain_single {P Q : α → Prop} (h : ∀ x, P x → Q x) (x : α) (hx : P x) :
    (Chain.cons Q h (Chain.nil Q)).out x :=
  compose_chain (Chain.cons Q h (Chain.nil Q)) x hx

/-- **空链是恒等**（第 59 轮的 `compose_sequential`）。 -/
theorem chain_nil_identity {P : α → Prop} (x : α) (hx : P x) :
    (Chain.nil P).out x :=
  compose_chain (Chain.nil P) x hx

/-- **两段的链**：逐段对照第 59 轮的 `compose_bridged`。 -/
theorem chain_two {P Q R : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, Q x → R x)
    (x : α) (hx : P x) :
    (Chain.cons Q h1 (Chain.cons R h2 (Chain.nil R))).out x :=
  compose_chain (Chain.cons Q h1 (Chain.cons R h2 (Chain.nil R))) x hx

/-! ## 四、衔接不可跳过 -/

/-- **无法跳过中间性质**：链的出口由其构造子逐段决定。

若一个链的出口是 `R`，那么 `R` 必然是某一层的 `Q`，或空链的 `P`。
这条定理把「衔接由类型强制」写成一个可检查的事实：
**`out` 只依赖链的构造，不依赖任何外部声明。** -/
theorem out_determined_by_construction {P R : α → Prop} (c : Chain α P) (h : c.out = R) :
    (c = Chain.nil P ∧ P = R) ∨
    (∃ (Q' : α → Prop) (hf : ∀ x, P x → Q' x) (rest : Chain α Q'),
        c = Chain.cons Q' hf rest ∧ rest.out = R) := by
  cases c with
  | nil P' =>
      left
      refine ⟨rfl, ?_⟩
      simpa [Chain.out] using h
  | cons Q hf rest =>
      right
      exact ⟨Q, hf, rest, rfl, h⟩

end MultiComposition

end Lattice.Audit
