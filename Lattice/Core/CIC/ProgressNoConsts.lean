import Mathlib
import Lattice.Core.CIC.ProgressEnv
import Lattice.Core.CIC.CanonicalForm
import Lattice.Core.CIC.ReductionOriented

/-!
# 进展定理：选定前提（`noConsts`）后的形式与边界（阶段 5）

## 第 804 轮留下了什么

**进展定理需要环境前提。本轮选定 `noConsts`（不可接受任何常量），并验证它确实排除了
`HasType.const`。**

## 本轮已完成

**`no_const_typed`：在 `noConsts` 下，`const c` **不可能**有任何类型。**

```lean
no_const_typed {Γ c A} : ¬ HasType noConsts Γ (.const c) A
```

**=> 这是第 804 轮那个反例 `app (const c) (var 0)` 被前提排除的**可检查形式**：
既然 `const c` 根本没有类型，那个项就无法构造。**

## 本轮**没有**完成的，以及为什么

**完整的进展定理需要对 `HasType` 派生归纳，`app` 情形再按 `f` 的**形状**分派。
后者要一条**

```lean
HasType noConsts Γ f (pi A B)  →  f = lam A' b  ∨  f = var n  ∨  f = app g x  ∨  f = letE ...
```

**的引理。本轮连写三次，三次都撞上同一个 Lean 限制：**

**`HasType` 是**三索引**归纳族（`Γ`、`t`、`A`）。对它的派生做 `induction` 时，
索引 `f` 与 `pi A B` 在目标里是**具体项**而非变量，Lean 报
「index in target's type is not a variable」。**

**=> 第 786 轮与第 801 轮都用过同一修法（把索引一般化成变量、事后以等式回代），
而这里 `f` 与 `A`、`B` **同时**是索引，一般化后还要处理三者之间的依赖 —— 本轮没有做到。**

## 结论

**进展定理的**前提**已选定并验证（`noConsts` 排除 `const`）。
剩余的**唯一**障碍是那条形状引理，而它的难点是 Lean 的索引一般化，不是数学。**

**本文件不声称进展定理已证。它给出前提的可检查形式，并把障碍精确定位到工具层面。** -/

namespace Lattice.Core.CIC

/-- **`noConsts` 下 `const` 不可类型化。**

**=> `HasType.const` 是唯一能类型化 `const` 的规则，而它要求 `noConsts c`，即 `False`。**
**这就是第 804 轮反例被前提排除的方式。** -/
theorem no_const_typed {Γ : CICCtx} {c : ℕ} {A : Term} :
    ¬ HasType noConsts Γ (.const c) A := by
  intro h
  cases h with
  | const _ _ _ hK => exact hK

/-- **`noConsts` 下的 `sort` 仍是良类型的。**

**=> 前提没有把系统清空：`HasType.sort` 不经过 `ConstSet`。** -/
theorem sort_typed_noConsts (Γ : CICCtx) (k : SortKind) (l : Level) :
    HasType noConsts Γ (.sort k l) (.sort k l) :=
  HasType.sort Γ k l

/-- **`noConsts` 下的 `lam` 仍是良类型的。**

**=> 第二个非平凡性检查：抽象规则也不经过 `ConstSet`。** -/
theorem lam_typed_noConsts (Γ : CICCtx) (A b B : Term) (h : HasType noConsts (A :: Γ) b B) :
    HasType noConsts Γ (.lam A b) (.pi A B) :=
  HasType.lam Γ A b B h

/-- **`noConsts` 下的 `app` 仍是良类型的。**

**=> 第三个非平凡性检查：应用规则经过函数部分的 `pi` 类型，而那条链上没有 `const`。** -/
theorem app_typed_noConsts (Γ : CICCtx) (f a : Term) (A B : Term)
    (hf : HasType noConsts Γ f (.pi A B)) (ha : HasType noConsts Γ a A) :
    HasType noConsts Γ (.app f a) B :=
  HasType.app Γ f a A B hf ha

end Lattice.Core.CIC
