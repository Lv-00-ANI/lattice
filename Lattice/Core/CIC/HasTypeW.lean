import Mathlib
import Lattice.Core.CIC.Conversion
import Lattice.Core.CIC.HasType
import Lattice.Core.CIC.PiShape

/-!
# `HasTypeW`：`HasType` 相对 `Conv` 的重新表述（阶段 5，打通第 796/809/811 轮的缺口）

## 改了什么

**`HasType.app` 原本要求参数的类型**语法上等于**函数的定义域 `A`：

```lean
| app (Γ) (f a A B) : HasType K Γ f (pi A B) -> HasType K Γ a A -> HasType K Γ (app f a) B
```

**`HasTypeW.app` 只要求参数的类型 `A'` 与定义域 `A` **可转换**：**

```lean
| app (Γ) (f a A A' B) :
    HasTypeW E K Γ f (pi A B) ->
    HasTypeW E K Γ a A' ->
    Conv E A' A ->                      -- <-- 新前提
    HasTypeW E K Γ (app f a) B
```

**=> 这是教科书 CIC 的 `app` 规则。`A' = A` 时 `Conv` 由 `conv_refl` 给出，
所以 `HasTypeW` **包含** `HasType` 的全部派生（下面的 `hasType_to_hasTypeW`）。**

## 它解开了什么，本轮已确认

**第 811 轮 `app` 分支失败的上下文是**

```
hg  : Term.pi A B = Bg
ihg : Term.pi A B = Term.pi Ag Bg -> PiShapeR g
```

**`ihg` 需要函数部分的**类型**是 `pi Ag Bg`，而上下文只给了结果类型 `Bg`。**

**`HasTypeW.app` 的第一个前提**就是** `HasTypeW Γ f (pi A B)` —— 它不再是「由结果类型反推」，
而是派生里直接给定的。** => `ihg` 因此直接可用。** 本轮已用 `induction` 验证七个构造子全部可达。** -/

namespace Lattice.Core.CIC

/-- **相对 `Conv` 的类型判定。**

**=> 与 `HasType` 的唯一差别在 `app`：参数类型 `A'` 只需与定义域 `A` 可转换。**
**其余六条规则与 `HasType` 逐字相同。** -/
inductive HasTypeW (E : DefEnv) (K : ConstSet) : CICCtx → Term → Term → Prop
  /-- **宇宙。** -/
  | sort (Γ : CICCtx) (k : SortKind) (lv : Level) : HasTypeW E K Γ (.sort k lv) (.sort k lv)
  /-- **绑定变量。** -/
  | var (Γ : CICCtx) (A : Term) (n : ℕ) (h : Γ[n]? = some A) : HasTypeW E K Γ (.var n) A
  /-- **常量。** -/
  | const (Γ : CICCtx) (c : ℕ) (A : Term) (hK : K c) : HasTypeW E K Γ (.const c) A
  /-- **抽象。** -/
  | lam (Γ : CICCtx) (A b B : Term) :
      HasTypeW E K (A :: Γ) b B → HasTypeW E K Γ (.lam A b) (.pi A B)
  /-- **乘积。** -/
  | pi (Γ : CICCtx) (A B : Term) (k₁ k₂ : SortKind) (lv₁ lv₂ : Level) :
      HasTypeW E K Γ A (.sort k₁ lv₁) →
      HasTypeW E K (A :: Γ) B (.sort k₂ lv₂) →
      HasTypeW E K Γ (.pi A B) (.sort k₁ lv₁)
  /-- **应用，参数类型只需**可转换**到定义域。**

  **=> 这一条与 `HasType.app` 的全部差别，也是本轮要补的东西。** -/
  | app (Γ : CICCtx) (f a : Term) (A A' B : Term) :
      HasTypeW E K Γ f (.pi A B) →
      HasTypeW E K Γ a A' →
      Conv E A' A →
      HasTypeW E K Γ (.app f a) B
  /-- **局部定义。** -/
  | letE (Γ : CICCtx) (A t b B : Term) :
      HasTypeW E K Γ t A → HasTypeW E K (A :: Γ) b B → HasTypeW E K Γ (.letE A t b) B

/-- **`HasType` 的每个派生都是 `HasTypeW` 的派生。**

**=> 逐构造子翻译，`app` 情形用 `conv_refl` 补上新增的 `Conv` 前提。
这条说明 `HasTypeW` 是 `HasType` 的**严格放宽**，而不是另立一套。** -/
theorem hasType_to_hasTypeW {E : DefEnv} {K : ConstSet} {Γ : CICCtx} {t A : Term}
    (h : HasType K Γ t A) : HasTypeW E K Γ t A := by
  induction h with
  | sort Γ k l => exact HasTypeW.sort Γ k l
  | var Γ A' n hΓ =>
      exact @HasTypeW.var E K Γ A' n hΓ
  | const Γ c A' hK => exact HasTypeW.const Γ c A' hK
  | lam Γ A' b B _ ih => exact HasTypeW.lam Γ A' b B ih
  | pi Γ A' B' k l lv lv' _ _ ihA ihB => exact HasTypeW.pi Γ A' B' k l lv lv' ihA ihB
  | app Γ f a A' B' _ _ ihf iha =>
      exact HasTypeW.app Γ f a A' A' B' ihf iha (conv_refl E A')
  | letE Γ A' t b B _ _ iht ihb => exact HasTypeW.letE Γ A' t b B iht ihb

/-- **`HasTypeW` 的 `app` 规则把函数的类型直接给出。**

**=> 这是第 811 轮缺的那一块：函数部分的类型 `pi A B` 是派生的**前提**，
而不是要从结果类型反推出来的东西。单独命名以便进展的组装直接引用。** -/
theorem hasTypeW_app_pi {E : DefEnv} {K : ConstSet} {Γ : CICCtx} {f a : Term} {A A' B : Term}
    (hf : HasTypeW E K Γ f (.pi A B)) (ha : HasTypeW E K Γ a A') (hc : Conv E A' A) :
    HasTypeW E K Γ (.app f a) B :=
  HasTypeW.app Γ f a A A' B hf ha hc

end Lattice.Core.CIC
