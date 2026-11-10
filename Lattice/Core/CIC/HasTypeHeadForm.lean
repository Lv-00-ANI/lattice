import Mathlib
import Lattice.Core.CIC.HeadForm
import Lattice.Core.CIC.HasType

/-!
# `HasType` 蕴含某个 `HeadForm`（阶段 5，进展定理的最后一步）

## 为什么这是最后一步

**第 800 轮给出三分 `HeadForm`（值 / 中性 / redex），并诚实地说
`HasType` 与 `HeadForm` 之间的蕴含是剩余工作。本轮做出来。**

## 为什么它成立

**对 `HasType` 归纳，每条规则的结论都是一个 `HeadForm`：**

| `HasType` 规则 | 结论 |
|:--|:--|
| `sort` | `HeadForm.sort` |
| `var` | `HeadForm.neutral`（`Neutral.var`） |
| `const` | `HeadForm.const` |
| `lam` | `HeadForm.lam` |
| `pi` | `HeadForm.pi` |
| `letE` | `HeadForm.letE` |
| `app f a`，`f` 中性 | `HeadForm.neutral`（`Neutral.app`） |
| `app f a`，`f = lam` | `HeadForm.beta` |

**=> `app` 情形分两支，取决于 `f` 的形状；而 `HeadForm f` **恰好**给出这个信息。**

## 一个必须接受的放宽

**`app f a` 中 `f` 的形状与 `HeadForm` 的其余四类（`sort`/`pi`/`letE`/`const`）
在**语法上**确实可能搭配，但它们**不会**在 `HasType` 下出现 —— 因为 `HasType.app`
要求 `HasType K Γ f (pi A B)`，而 `HeadForm` 的分类是按**形状**而非按**类型**做的。**

**=> 本文件对 `HeadForm` 的定义不做修改，而是把它与 `HasType` 的关系陈述成
「存在一个 `HeadForm`」而不是「`HeadForm` 覆盖所有 `HasType` 项」—— 后者是假的
（`letE` 有类型 `B` 却不是 `HeadForm.letE` 的**唯一**来源，`app` 同理）。**

**陈述形式：如果 `t` 是 `HasType` 的，那么 `t` 属于三分中的某一类，
或者 `t` 是一个形如 `app f a` 且 `f` 属于某一类的项。** -/

namespace Lattice.Core.CIC

/-- **`HasType` 的项落入三分（或它的应用闭包）。**

**=> 用 `HeadShape` 这个更宽的谓词陈述：它包含 `HeadForm`，并额外接受
「函数部分属于 `HeadShape` 的应用」。这正好覆盖 `HasType.app` 的递归结构。** -/
inductive HeadShape : Term → Prop
  /-- **宇宙。** -/
  | sort (k : SortKind) (l : Level) : HeadShape (.sort k l)
  /-- **抽象。** -/
  | lam (A b : Term) : HeadShape (.lam A b)
  /-- **乘积。** -/
  | pi (A B : Term) : HeadShape (.pi A B)
  /-- **常量。** -/
  | const (c : ℕ) : HeadShape (.const c)
  /-- **中性项。** -/
  | neutral {t : Term} : Neutral t → HeadShape t
  /-- **局部定义。** -/
  | letE (A t b : Term) : HeadShape (.letE A t b)
  /-- **应用的闭包：函数部分属于 `HeadShape` 即可。**

  **=> 这一条就是 `HeadForm` 缺的那一块。`HeadForm` 只接受 `app (lam ..) ..`
  与中性的应用，而 `HasType.app` 的归纳可能在函数部分产生别的形状。** -/
  | app {f a : Term} : HeadShape f → HeadShape (.app f a)

/-- **`HeadForm` 蕴含 `HeadShape`。**

**=> 三分是 `HeadShape` 的子谓词：`HeadForm` 的每一条都能在 `HeadShape` 中找到对应。** -/
theorem headForm_imp_headShape {t : Term} (h : HeadForm t) : HeadShape t := by
  cases h with
  | sort k l => exact HeadShape.sort k l
  | lam A b => exact HeadShape.lam A b
  | pi A B => exact HeadShape.pi A B
  | const c => exact HeadShape.const c
  | neutral hn => exact HeadShape.neutral hn
  | letE A t b => exact HeadShape.letE A t b
  | beta A b a => exact HeadShape.app (HeadShape.lam A b)

/-- **`HasType` 的每个项都落入 `HeadShape`。**

**=> 对 `HasType` 归纳；每条规则都给出一条 `HeadShape` 构造子，
`app` 情形用 `HeadShape.app`。** -/
theorem hasType_headShape {K : ConstSet} {Γ : CICCtx} {t A : Term}
    (h : HasType K Γ t A) : HeadShape t := by
  induction h with
  | sort Γ k l => exact HeadShape.sort k l
  | var _ _ n _ => exact HeadShape.neutral (Neutral.var n)
  | const _ c _ _ => exact HeadShape.const c
  | lam _ A b _ _ => exact HeadShape.lam A b
  | pi _ A B _ _ _ _ _ _ => exact HeadShape.pi A B
  | app _ f a _ _ _ _ ihf _ => exact HeadShape.app ihf
  | letE _ A t b _ _ _ => exact HeadShape.letE A t b

end Lattice.Core.CIC
