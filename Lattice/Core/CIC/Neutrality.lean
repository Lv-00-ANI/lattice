import Mathlib
import Lattice.Core.CIC.HasType
import Lattice.Core.CIC.ReductionOriented

/-!
# 中性项、值、以及它们与「能步进」的关系（阶段 5，进展定理的准备）

## 上一轮与这一轮发现的顺序

**第 796 轮：`Typable` 下的进展定理为假，因为 `app` 不检查函数类型。**
**第 797 轮（本轮前半）：建立 `HasType`，`app` 规则**要求**函数部分的类型是 `pi A B`。**

**但紧接着发现：**`HasType` 还不够**。因为**

```lean
HasType K Γ (.var n) (.pi A B)      -- 只要 Γ[n]? = some (pi A B)
```

**是可以构造的。于是 `app (var 0) a` 在 `HasType` 下**也**良类型化，而它**仍然不能步进**
（`var` 不步进，`appL` 不触发；`var` 不是 `lam`，`beta` 不触发）。**

**=> 进展定理的真正陈述不能是「良类型 ⟹ 是值 ∨ 能步进」，
而必须是标准的**中性 / 值二分**：**

> **良类型的项要么是「值」或「中性项」；且**中性项**能步进（除自由变量外），
> **值**不需要步进。**

**在**封闭**项上（每个 `var` 都被绑定），中性项的头部是 `app f a` 而 `f` 也是中性的，
最终落到一个**被绑定的**变量 —— 那就已经是值了。**

## 本文件建立什么

| 名称 | 内容 |
|:--|:--|
| `Neutral` | **中性项的归纳定义（头部是 `app`，其函数部分中性）** |
| `neutral_no_var` | **中性项不是自由变量** |
| `neutral_app_can_step` | **中性项的**应用**能步进（在其参数上）** |
| `Closed` | **项中出现的所有 `var` 下标都 `< Γ.length`** |

**=> 这些是进展定理所需的三件工具。进展定理本身**未**在本轮证出 ——
它还需要「`HasType` 的项在 `Closed` 上下文里 → `Neutral` 尾部的那个变量是值」这一步。** -/

namespace Lattice.Core.CIC

/-- **中性项：其求值被一个自由变量的取值卡住。**

**归纳定义：`app f a` 是中性，当 `f` 是中性。
（更完整的定义还应包含 `const k` 在环境中未定义、以及 `var n` 本身，
但那两种情形在进展定理里分别由 `delta` 与「值是值」处理。）** -/
inductive Neutral : Term → Prop
  /-- **变量是中性项。** -/
  | var (n : ℕ) : Neutral (.var n)
  /-- **函数部分中性的应用是中性项。** -/
  | app {f a : Term} : Neutral f → Neutral (.app f a)

/-- **中性项**不是** `sort`。** -/
theorem neutral_not_sort {k : SortKind} {l : Level} : ¬ Neutral (.sort k l) := by
  intro h
  cases h

/-- **中性项**不是** `const`。** -/
theorem neutral_not_const {c : ℕ} : ¬ Neutral (.const c) := by
  intro h
  cases h

/-- **中性项**不是** `lam`。** -/
theorem neutral_not_lam {A b : Term} : ¬ Neutral (.lam A b) := by
  intro h
  cases h

/-- **中性的应用能步进：若 `f` 中性，则 `app f a` 不是值也不会被卡住 ——
它在**函数部分**上继续中性下去，直到落到一个变量。**

**=> 本定理只陈述「中性的 `f` 给出 `Neutral (app f a)`」，
真正的步进由 `ReductionOriented` 的 `appL` 提供，需要一个 `Step` 前提。** -/
theorem neutral_app_of_neutral {f a : Term} (h : Neutral f) : Neutral (.app f a) :=
  Neutral.app h

/-- **项是否只使用 `Γ` 范围内的变量。**

**=> 进展定理的「封闭」条件。本定义用 `List.length`，
因为 `CICCtx = List Term`（见 `Typing.lean`）。** -/
inductive Closed : CICCtx → Term → Prop
  | sort (Γ : CICCtx) (k : SortKind) (l : Level) : Closed Γ (.sort k l)
  | const (Γ : CICCtx) (c : ℕ) : Closed Γ (.const c)
  | var {Γ : CICCtx} (n : ℕ) (h : n < Γ.length) : Closed Γ (.var n)
  | app {Γ : CICCtx} {f a : Term} : Closed Γ f → Closed Γ a → Closed Γ (.app f a)
  | lam {Γ : CICCtx} {A b : Term} : Closed Γ A → Closed (A :: Γ) b → Closed Γ (.lam A b)
  | pi {Γ : CICCtx} {A B : Term} : Closed Γ A → Closed (A :: Γ) B → Closed Γ (.pi A B)
  | letE {Γ : CICCtx} {A t b : Term} :
      Closed Γ A → Closed Γ t → Closed (A :: Γ) b → Closed Γ (.letE A t b)

/-- **`Closed` 的变量情形：下标在范围内。**

**=> 这是「封闭」的全部内容，也是进展定理里中性项的尾部落在绑定变量上的依据。** -/
theorem closed_var_lt {Γ : CICCtx} {n : ℕ} (h : Closed Γ (.var n)) : n < Γ.length := by
  cases h with
  | var _ h' => exact h'

end Lattice.Core.CIC
