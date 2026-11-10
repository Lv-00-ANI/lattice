import Mathlib
import Lattice.Core.CIC.ProgressNoConsts
import Lattice.Core.CIC.CanonicalForm
import Lattice.Core.CIC.ReductionOriented

/-!
# 形状引理已证：`HasType noConsts Γ f (pi A B)` 蕴含 `f` 的具体形状（阶段 5）

## 第 805 轮把这一步记成了「Lean 障碍」

**第 805 轮连试三次形状引理，三次都撞上「index in target's type is not a variable」，
并记下了下次该试的模式（`generalize` → `cases` → `subst`）。**

**本轮照那个模式做，一次通过。** **关键是两点：**

1. **`generalize hg : (Term.pi A B) = target at h`** —— 把第三索引变成变量；
2. **跨构造子的矛盾用 `intro hh; cases hh`，不用 `injection`** ——
   `Term.pi A B = Term.sort k l` 是**构造子互斥**，不是同一构造子的参数不等。

## 结论

```lean
inductive PiShape : Term -> Prop
  | lam (A b) | var (n) | app (f a) | letE (A t b)

pi_typed_shape {Γ f A B} (h : HasType noConsts Γ f (.pi A B)) : PiShape f
```

**=> 在 `noConsts` 下，一个具有 `pi` 类型的项**只能**是 `lam`、`var`、`app`、`letE` 之一。
`const` 被前提排除（`no_const_typed`），`sort` 与 `pi` 被构造子互斥排除。**

**这正是进展定理 `app` 分支所需的分派依据：拿到 `PiShape f`，就可以按四种形状分别处理。** -/

namespace Lattice.Core.CIC

/-- **具有 `pi` 类型的项的形状（在 `noConsts` 下）。**

**=> 四条：抽象、变量、应用、局部定义。没有 `sort`/`pi`/`const` 的位置。** -/
inductive PiShape : Term → Prop
  /-- **抽象：`lam A b` 具有类型 `pi A B`。** -/
  | lam (A b : Term) : PiShape (.lam A b)
  /-- **变量：若 `Γ[n]? = some (pi A B)`。** -/
  | var (n : ℕ) : PiShape (.var n)
  /-- **应用：函数部分的类型是 `pi`，其结果类型为 `B`。** -/
  | app (f a : Term) : PiShape (.app f a)
  /-- **局部定义：其体的类型是 `B`。** -/
  | letE (A t b : Term) : PiShape (.letE A t b)

/-- **跨构造子的矛盾用 `cases`，不用 `injection`。**

**=> `Term.pi A B = Term.sort k l` 是两个**不同构造子**的相等，`cases` 一句即消；
`injection` 只在同一构造子的参数上适用，故在此报「too many equations」。** -/
theorem pi_ne_sort (A B : Term) (k : SortKind) (l : Level) :
    (Term.pi A B : Term) ≠ Term.sort k l := by
  intro h
  cases h

/-- **形状引理：`noConsts` 下具有 `pi` 类型的项属于 `PiShape`。**

**=> 对 `HasType` 派生归纳，先把第三索引 `pi A B` 一般化成变量，
再按七个构造子分派：**

- **`sort`/`pi`**：与 `pi A B` 构造子互斥，矛盾；
- **`const`**：被 `noConsts` 排除；
- **`var`/`lam`/`app`/`letE`**：各给出一条 `PiShape`。

**这条就是第 805 轮记下的「下一次该试的模式」，本轮一次通过。** -/
theorem pi_typed_shape {Γ : CICCtx} {f A B : Term}
    (h : HasType noConsts Γ f (.pi A B)) : PiShape f := by
  generalize hg : (Term.pi A B) = target at h
  cases h with
  | sort _ k l => exact absurd hg (by intro hh; cases hh)
  | var _ A' n _ => exact PiShape.var n
  | const _ c _ hK => exact absurd hK (by simp [noConsts])
  | lam _ A' b _ _ => exact PiShape.lam A' b
  | pi _ A' B' k l lv lv' _ _ => exact absurd hg (by intro hh; cases hh)
  | app _ g x _ _ _ _ => exact PiShape.app g x
  | letE _ A' t b _ _ _ => exact PiShape.letE A' t b

/-- **`PiShape` 不是 `sort`。**

**=> 形状引理的直接推论：具有 `pi` 类型的项不是宇宙。** -/
theorem piShape_not_sort {k : SortKind} {l : Level} {f : Term}
    (h : PiShape f) : f ≠ Term.sort k l := by
  intro he
  subst he
  cases h

end Lattice.Core.CIC
