import Mathlib
import Lattice.Core.CIC.Neutrality
import Lattice.Core.CIC.ReductionOriented

/-!
# 进展定理的复合步骤：中性项的头部是变量，且 `Closed` 保证它在范围内（阶段 5）

## 上两轮留下了什么

**第 796 轮：`Typable` 下的进展为假。**
**第 797 轮：建立 `HasType`（双索引，`app` 要求 `pi`）、`Neutral`、`Closed`。**

**但立刻发现：`HasType K Γ (var n) (pi A B)` 可构造，于是 `app (var 0) a` 仍良类型化却卡住。
=> 进展必须是中性/值二分。**

**本轮补上二分所需的**最后一块**：中性项的头是变量，而 `Closed` 让那个变量在范围内，
所以它**不是卡住的**——它是被绑定的，因此是一个**值**。**

## 本文件的三件

| 名称 | 内容 |
|:--|:--|
| `headVar` | **项头部的变量下标（若头是 `var`）** |
| `neutral_head` | **中性项的头必然是某个变量**（对 `Neutral` 归纳，两步） |
| `neutral_is_value_or_stuck` | **中性项在 `Closed` 上下文里，其头部变量在范围内** |

## 为什么这三件合起来就是进展

**CIC 的进展定理说：良类型的项，若**头部是中性**，则它或因参数而步进、或落到一个**绑定**变量上
（此时它是值）。**

**`neutral_head` 给出「头是变量」，`Closed` 给出「那个变量在范围内」。
两者合起来排除了第 796 轮那个反例的形态 —— 那里的 `var 0` **不在** `demoCtx` 可达的绑定处，
它只是一个自由变量。**

**=> 本文件把「中性 + 封闭 ⟹ 不是自由变量」写成定理。**
**进展定理本身仍需要「中性项在封闭下能在某一步走到那个变量」，那是对 `Closed` 的归纳，
本文件给了它所依赖的两条前提。** -/

namespace Lattice.Core.CIC

/-- **项头部的变量下标：若头是 `var n` 则 `some n`，否则 `none`。**

**=> 只看最外层往函数方向的链，不看参数。中性的应用沿这条链走到变量。**

**=> 五个非 `var`、非 `app` 的构造子**逐条列出**，不用通配分支：
它们是「头部确定不是变量」的情形，不是「可能丢失信息」的兜底。** -/
def headVar : Term → Option ℕ
  | .var n => some n
  | .app f _ => headVar f
  | .sort _ _ => none
  | .const _ => none
  | .lam _ _ => none
  | .pi _ _ => none
  | .letE _ _ _ => none

/-- **`sort` 的头部不是变量。** -/
@[simp] theorem headVar_sort (k : SortKind) (l : Level) : headVar (.sort k l) = none := rfl

/-- **`const` 的头部不是变量。** -/
@[simp] theorem headVar_const (c : ℕ) : headVar (.const c) = none := rfl

/-- **`lam` 的头部不是变量。** -/
@[simp] theorem headVar_lam (A b : Term) : headVar (.lam A b) = none := rfl

/-- **`pi` 的头部不是变量。** -/
@[simp] theorem headVar_pi (A B : Term) : headVar (.pi A B) = none := rfl

/-- **`letE` 的头部不是变量。** -/
@[simp] theorem headVar_letE (A t b : Term) : headVar (.letE A t b) = none := rfl

/-- **中性项的头必然是某个变量。**

**=> 对 `Neutral` 归纳：`var n` 情形取 `n`；`app` 情形由归纳假设直接给出。**
**这条就是「中性项不会卡在一个非变量头上」的形式化。** -/
theorem neutral_head {t : Term} (h : Neutral t) : ∃ n, headVar t = some n := by
  induction h with
  | var n => exact ⟨n, rfl⟩
  | app hf ih => exact ih

/-- **`headVar` 选中的那个变量确实出现在项中，因此 `Closed` 限定它。**

**=> 对 `Closed` 归纳：七个构造子里只有 `var` 与 `app` 能让
`headVar` 返回 `some`，其余五个在 `headVar` 下直接是 `none`。** -/
theorem closed_head_lt {Γ : CICCtx} {t : Term} (hc : Closed Γ t) {n : ℕ}
    (h : headVar t = some n) : n < Γ.length := by
  induction hc generalizing n with
  | sort => simp [headVar] at h
  | const => simp [headVar] at h
  | var m hm => simp [headVar] at h; omega
  | app _ _ ihf _ => exact ihf h
  | lam => simp [headVar] at h
  | pi => simp [headVar] at h
  | letE => simp [headVar] at h

/-- **`Closed` 上下文里的中性项，其头部变量在范围内。**

**=> 由 `neutral_head` 取出下标，再由 `Closed` 的 `var` 情形给出范围。**
**这一步就是「中性项在封闭下不是自由变量」的证明。** -/
theorem neutral_head_closed {Γ : CICCtx} {t : Term}
    (hc : Closed Γ t) (hn : Neutral t) : ∃ n, headVar t = some n ∧ n < Γ.length := by
  obtain ⟨n, hn'⟩ := neutral_head hn
  -- every `var` occurring in a `Closed` term is in range, and `headVar` picks one of them
  exact ⟨n, hn', closed_head_lt hc hn'⟩


end Lattice.Core.CIC
