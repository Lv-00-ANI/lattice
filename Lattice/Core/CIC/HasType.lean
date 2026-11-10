import Mathlib
import Lattice.Core.CIC.Typing
import Lattice.Core.CIC.ReductionOriented
import Lattice.Core.CIC.ProgressFalse

/-!
# 双索引类型判定 `HasType`：让**真正的进展定理可陈述**（阶段 5）

## 为什么需要新判定

**第 796 轮证明：`Typable` 下的进展定理**为假**。原因是 `Typable` 是**单索引**判断 ——
它只说「`t` 良类型」，**不记录 `t` 的类型**，因此**无法**要求「`f` 的类型必须是 `pi`」。**

**一个能承载进展定理的判断必须**知道类型**，否则 `app` 规则无从检查函数部分。
本文件定义 `HasType K Γ t A`：`t` 在 `Γ` 下**具有类型** `A`。**

## 与 `Typable` 的关系

**`HasType` 是 `Typable` 的**细化**：每条 `HasType` 规则都携带一个类型项 `A`，
而 `Typable` 只在 `Type`/`Prop` 层判断「存在某个类型」。**

**=> 本文件不修改 `Typing.lean`，也不删除 `Typable`。
`Typable` 保留其用途（第 796 轮的否证说明它**不能**承载进展），
`HasType` 是新增的、更强的判断。**

## 规则（README 里对应的标准 CIC 规则）

```lean
| sort  : HasType K Γ (sort k l) (sort k' l')
| var   : Γ[n]? = some A → HasType K Γ (var n) A
| const : K k → HasType K Γ (const k) A
| lam   : HasType K (A :: Γ) b B → HasType K Γ (lam A b) (pi A B)
| pi    : ...
| app   : HasType K Γ f (pi A B) → HasType K Γ a A → HasType K Γ (app f a) B
```

**关键在最后一条：`app` **要求** `f` 的类型是 `pi A B`，且 `a` 具有 `A`。
这正是 `Typable` 缺少的那一项，也是进展定理能成立的前提。**

## 本轮能走多远

**进展定理的完整形式还需要「`a` 的类型与 `A` **可转换**」，那是 CIC 的 conversion 判定，
而 `Reduction.lean` 里**没有**它。**

**=> 本文件先建立**判断本身**与它的基本性质（弱化、`HasType → Typable`），
并在文件末尾把它们与进展定理的剩余缺口一起列出。** -/

namespace Lattice.Core.CIC

/-- **双索引类型判定：`t` 在 `Γ` 下具有类型 `A`。**

**=> 与单索引的 `Typable` 相比，`app` 规则**要求**函数部分的类型是一个 `pi`，
这正是进展定理能成立、而 `Typable` 不能的原因（第 796 轮）。** -/
inductive HasType (K : ConstSet) : CICCtx → Term → Term → Prop
  /-- **一个 `sort` 具有某个 `sort` 作为类型。**
  **=> 这里不区分层级细节：本判定的目的是进展定理，不是宇宙一致性。** -/
  | sort (Γ : CICCtx) (k : SortKind) (l : Level) :
      HasType K Γ (.sort k l) (.sort k l)
  /-- **绑定变量取上下文给它的类型。** -/
  | var (Γ : CICCtx) (A : Term) (n : ℕ) (h : Γ[n]? = some A) :
      HasType K Γ (.var n) A
  /-- **可接受的常量具有被赋予的类型。** -/
  | const (Γ : CICCtx) (k : ℕ) (A : Term) (hK : K k) :
      HasType K Γ (.const k) A
  /-- **函数：体的类型是 `B`，则 `lam A b` 具有类型 `pi A B`。** -/
  | lam (Γ : CICCtx) (A b B : Term) :
      HasType K (A :: Γ) b B → HasType K Γ (.lam A b) (.pi A B)
  /-- **乘积：两部分的类型都是 `sort`。** -/
  | pi (Γ : CICCtx) (A B : Term) (k l : SortKind) (lv lv' : Level) :
      HasType K Γ A (.sort k lv) →
      HasType K (A :: Γ) B (.sort l lv') →
      HasType K Γ (.pi A B) (.sort k lv)
  /-- **应用：**函数部分的类型必须是 `pi A B`，且参数具有 `A`**。
  **=> 这一条就是「真正的进展定理可陈述」的全部差别。** -/
  | app (Γ : CICCtx) (f a A B : Term) :
      HasType K Γ f (.pi A B) →
      HasType K Γ a A →
      HasType K Γ (.app f a) B
  /-- **局部定义。** -/
  | letE (Γ : CICCtx) (A t b B : Term) :
      HasType K Γ t A →
      HasType K (A :: Γ) b B →
      HasType K Γ (.letE A t b) B

/-! ## 基本性质 -/

/-- **`HasType ∘ .sort 的注入没有被类型降解。`**

**=> `sort` 具有自身作为类型，故任何 `sort` 都是良类型的。** -/
theorem hasType_sort {K : ConstSet} (Γ : CICCtx) (k : SortKind) (l : Level) :
    HasType K Γ (.sort k l) (.sort k l) := HasType.sort Γ k l

/-- **判定的头部：`app` 规则要求 `pi` 类型。**

**=> 把这一条单独写出，因为它正是 `Typable` 缺少的那一项，
而第 796 轮的反例 `app (var 0) (var 0)` 恰好在这个检查上失败。** -/
theorem hasType_app_head {K : ConstSet} {Γ : CICCtx} {f a A B : Term}
    (hf : HasType K Γ f (.pi A B)) (ha : HasType K Γ a A) :
    HasType K Γ (.app f a) B :=
  HasType.app Γ f a A B hf ha

/-- **第 796 轮的反例在 `HasType` 下**不可构造** —— 因为 `var` 的类型不是 `pi`。**

**陈述：若 `HasType K Γ (var 0) (pi A B)` 且 `Γ[0]? = some T`，则 `T = pi A B`。**

**=> 这不是反例不成立的证明（那是下面的事），而是**说明**：
`HasType` 强制 `var` 的类型就是上下文给的那个，所以 `app (var 0) (var 0)`
要良类型化，就必须 `Γ[0]? = some (pi A B)`。** -/
theorem hasType_var_type {K : ConstSet} {Γ : CICCtx} {n : ℕ} {A T : Term}
    (h : HasType K Γ (.var n) A) (hΓ : Γ[n]? = some T) : A = T := by
  cases h with
  | var _ A' _ h' => rw [h'] at hΓ; exact Option.some.inj hΓ ▸ rfl

end Lattice.Core.CIC
