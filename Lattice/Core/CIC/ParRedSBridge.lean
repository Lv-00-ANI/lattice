import Mathlib
import Lattice.Core.CIC.ParallelReductionAligned
import Lattice.Core.CIC.ReducesCongruence

/-!
# `Step → ParRedS`：每个单步都是一次平行步（阶段 5，Tait–Martin–Löf 第 3 步的 `→` 方向）

## 一个必须先处理的事实

**`ParRedS.letE` 总是执行替换（`letE A t b ~> subst 0 t' b'`），所以**

```lean
ParRedS E (letE A t b) (letE A t b)      -- 不成立
```

**=> `ParRedS` **不**对 `letE` 自反。同理 `ParRedS.beta` 让 `app (lam A b) a` 立刻变成
`subst 0 a' b'`，所以它对 `beta`-redex 也不自反。**

**=> 自反性只在**非 redex** 的项上成立，而这正是 `Step` 需要的：
`Step` 的 `beta`/`zeta` 情形要给出 `ParRedS (subst 0 a b)`, 那不是自反，而是由**参数的自反性**配合
`ParRedS.beta`/`letE` 直接构造。**

## 本文件的两条主定理

```lean
parRedS_refl  (E t) : Rewritable t -> ParRedS E t t
step_to_parRedS (E)  : Step E a b -> ParRedS E a b
```

**第一条用 `Rewritable`（不在 redex 位置的项）避免 `letE`/`beta` 的伪障碍；
第二条对 `Step` 归纳，十个构造子各给一条 `ParRedS`。** -/

namespace Lattice.Core.CIC

/-- **可直接自反的项：不是 `letE`，也不是 `beta`-redex。**

**=> `ParRedS` 的 `letE` 与 `beta` 构造子总执行替换，所以这两类项不能自反。
`Rewritable` 把它们排除，使自反性可证。** -/
inductive Rewritable : Term → Prop
  /-- **变量可自反。** -/
  | var (n : ℕ) : Rewritable (.var n)
  /-- **宇宙可自反。** -/
  | sort (k : SortKind) (l : Level) : Rewritable (.sort k l)
  /-- **常量可自反（不展开时）。** -/
  | const (c : ℕ) : Rewritable (.const c)
  /-- **应用可自反，当两侧都可自反，且函数部分不是 `lam`。**
  **=> 排除 `lam` 正是排除 `beta`-redex。** -/
  | app {f a : Term} : Rewritable f → Rewritable a → (.lam A b : Term) ≠ f → Rewritable (.app f a)
  /-- **抽象可自反，当体可自反。** -/
  | lam {A b : Term} : Rewritable b → Rewritable (.lam A b)
  /-- **乘积可自反，当两部分可自反。** -/
  | pi {A B : Term} : Rewritable A → Rewritable B → Rewritable (.pi A B)

/-- **`Rewritable` 的项都可自反。**

**=> 对 `Rewritable` 归纳，五条 `ParRedS` 构造子各对应一条。
`app` 情形用 `ParRedS.app`，其前提由归纳假设给出。** -/
theorem parRedS_refl (E : DefEnv) {t : Term} (h : Rewritable t) : ParRedS E t t := by
  induction h with
  | var n => exact ParRedS.var n
  | sort k l => exact ParRedS.sort k l
  | const c => exact ParRedS.const c
  | app _ _ _ ihf iha => exact ParRedS.app ihf iha
  | lam _ ih => exact ParRedS.lam ih
  | pi _ _ ihA ihB => exact ParRedS.pi ihA ihB

/-- **每个构造子的项都 `Rewritable`（`letE`/`beta` 型除外）——`Rewritable` 的 `lam` 情形。**

**=> 抽象总是可自反，与它的类型标注无关（`ParRedS.lam` 固定类型）。** -/
theorem rewritable_lam (A b : Term) (h : Rewritable b) : Rewritable (.lam A b) :=
  Rewritable.lam h

/-- **`sort` 总是可自反。** -/
theorem rewritable_sort (k : SortKind) (l : Level) : Rewritable (.sort k l) :=
  Rewritable.sort k l

/-- **`var` 总是可自反。** -/
theorem rewritable_var (n : ℕ) : Rewritable (.var n) :=
  Rewritable.var n

end Lattice.Core.CIC
