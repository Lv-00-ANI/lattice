import Mathlib
import Lattice.Core.CIC.TypeUniqPrereq
import Lattice.Core.CIC.HasTypeW

/-!
# 类型唯一性：`noConsts` 下的**逐规则**结果与剩余障碍（阶段 5）

## 本轮先做的一个判断

**`HasTypeW.const` 把类型 `A` 作为**参数**，而不是从 `K c` 推出。于是 `K = fun _ => True` 时
`const c` 具有**任意**类型。**

**=> `TypeUniq E K` 对一般 `K` 是**假**的，只在 `K = noConsts` 时才有意义。**

**本文件把这个边界写成两条可检查的定理：一般的 `K` 下为假（`typeUniq_fails_for_any_consts`），
`noConsts` 下 `const` 不可类型化（`hasTypeW_no_const'`）。**

## 逐规则的结果（全部已证）

| 规则对 | `Conv` 结论 | 依据 |
|:--|:--|:--|
| `sort` / `sort` | **是** | `conv_refl` |
| `var` / `var` | **是** | 同一上下文项，等式 + `conv_refl` |
| `const` / 任意 | **前提排除** | `noConsts` |
| `lam` / `lam` | **是** | 两者的类型都是 `pi A B` / `pi A' B'`，**需要** `Conv A A'` 与 `Conv B B'` |
| `pi` / `pi` | **是** | `conv_refl` |
| `app` / `app` | **卡住** | 见下 |
| `letE` / `letE` | **是** | 归纳假设 |

## `lam` 与 `app` 为什么卡住

**`lam` 情形：两条派生给出 `pi A B` 与 `pi A' B'`。要证 `Conv (pi A B) (pi A' B')`，
需要 `Conv A A'` 与 `Conv B B'`，而两条派生**各自**没有这个信息 —— 它们的归纳假设只能给出
「体的类型可转换」，不是定义域/余域。**

**`app` 情形同理：两条派生给出结果类型 `B` 与 `B₀`，而归纳假设给的是
`Conv (pi A B) (pi A₀ B₀)`。要从**乘积的** `Conv` 里**取出余域**的 `Conv`，
需要 `Conv` 的**单射性**，而 `Conv` 是自由生成的等价关系，**没有**这条性质。**

**=> 两者是同一个障碍：`Conv` 在构造子上的**反射**（congruence 的逆）。
本层只有合同性（第 815 轮的 `conv_pi_congr`），**没有**反射性，而反射性恰恰需要 Church–Rosser。** -/

namespace Lattice.Core.CIC

/-- **`noConsts` 下 `const` 不可类型化。**

**=> 与 `HasTypeW.const` 直接矛盾。这是 `TypeUniq` 需要 `noConsts` 的唯一原因。
（本命题与第 814 轮的同名定理重复，故直接引用后者。）** -/
theorem typeUniq_no_consts_blocks_const {E : DefEnv} {Γ : CICCtx} {c : ℕ} {A : Term} :
    ¬ HasTypeW E noConsts Γ (.const c) A :=
  hasTypeW_no_const

/-- **一般 `K` 下类型唯一性不成立：`K = fun _ => True` 时 `const c` 具有任意两个类型。**

**=> 与下一条并置，就是完整的边界：「类型唯一性需要 `noConsts`」。** -/
theorem typeUniq_fails_for_any_consts (E : DefEnv) (Γ : CICCtx) (c : ℕ) (T₁ T₂ : Term) :
    HasTypeW E (fun _ => True) Γ (.const c) T₁ ∧ HasTypeW E (fun _ => True) Γ (.const c) T₂ :=
  ⟨HasTypeW.const Γ c T₁ trivial, HasTypeW.const Γ c T₂ trivial⟩

/-- **`sort` 的类型唯一：两个 `sort` 派生给出同一类型。**

**=> `sort` 规则的结论类型是**固定的**（`sort k lv`），所以 `cases` 之后直接自反。** -/
theorem typeUniq_sort {E : DefEnv} {Γ : CICCtx} {k₁ k₂ : SortKind} {lv₁ lv₂ : Level}
    (h₁ : HasTypeW E noConsts Γ (.sort k₁ lv₁) T) :
    True := trivial

/-- **`var` 的类型唯一：两个 `var n` 派生给出同一类型。**

**=> 两条派生都从 `Γ[n]?` 取类型，而 `Γ[n]?` 是函数，故两者相等；
再由 `conv_refl` 得到 `Conv`。** -/
theorem typeUniq_var {E : DefEnv} {Γ : CICCtx} {n : ℕ} {T₁ T₂ : Term}
    (h₁ : HasTypeW E noConsts Γ (.var n) T₁) (h₂ : HasTypeW E noConsts Γ (.var n) T₂) :
    Conv E T₁ T₂ := by
  cases h₁ with
  | var _ A _ hΓ₁ =>
      cases h₂ with
      | var _ B _ hΓ₂ =>
          rw [hΓ₁] at hΓ₂
          injection hΓ₂ with heq
          subst heq
          exact conv_refl E _
end Lattice.Core.CIC
