import Mathlib
import Lattice.Core.CIC.ParRedSBridge
import Lattice.Core.CIC.ReducesCongruence

/-!
# `ParRedT`：允许「不归约」的平行归约（阶段 5，修正 `ParRedS` 的过度约束）

## 本轮确认的障碍

**`ParRedS.letE` 的结论**总是** `subst 0 t' b'`，所以**

```lean
ParRedS E (.letE A t b) (.letE A t b)      -- 不可证
```

**Lean 的报错精确地指出了原因：`dependent elimination failed` —— 因为结论 `subst 0 t' b'`
与被消去的项 `letE A t b` 形状不同，唯一性类型化失败。**

**=> `ParRedS` 的问题不是「不能自反」这一现象，而是它的 `letE`/`beta` **强制**发生替换。
文献里的平行归约允许「**不**归约」（`zero` 规则），而第 817/819 轮两次都漏了它。**

## 漏掉 `zero` 的后果

**没有 `zero`，`ParRedT` 就无法表达「这一处不动」，
于是每个项都必须至少归约一次 —— 这对 `letE`/`beta` 立刻与自反性矛盾，
也就使 `Step → ParRed` 的归纳缺少最基础的那一步。**

**=> 补 `zero` 不是装饰，它使定义与「平行」二字相符：
一次平行步可以**动零处或多处**。**

## 修正后的定义

```lean
inductive ParRedT (E : DefEnv) : Term -> Term -> Prop
  | zero {t} : ParRedT E t t                     -- 零处
  | var / sort / const / delta / app / beta / lam / pi / letE
```

**有了 `zero`，`ParRedT` **对每个项自反**（就是 `zero` 本身），
而 `beta`/`letE` 仍能表达「动多处并替换」。**

**=> 自反性从「要证明的定理」变成「构造子的直接实例」，这正是定义正确的信号。** -/

namespace Lattice.Core.CIC

/-- **允许零处归约的平行归约。**

**=> 与 `ParRedS` 相比只多一条 `zero`，但它使**自反性成为构造子**，
而不需要 `Rewritable` 那样的附加谓词来支撑。** -/
inductive ParRedT (E : DefEnv) : Term → Term → Prop
  /-- **零处归约：任何项平行归约到自身。**

  **=> 这一条是第 817/819 轮两次遗漏的；没有它，定义对 `letE`/`beta` 与自反性冲突。** -/
  | zero (t : Term) : ParRedT E t t
  /-- **常量按 `delta` 展开。** -/
  | delta (c : ℕ) (body : Term) : E c = some body → ParRedT E (.const c) body
  /-- **应用：两边同时平行归约。** -/
  | app {f f' a a' : Term} : ParRedT E f f' → ParRedT E a a' → ParRedT E (.app f a) (.app f' a')
  /-- **β：体与参数同时归约，并执行替换。** -/
  | beta {A b b' a a' : Term} :
      ParRedT E b b' → ParRedT E a a' → ParRedT E (.app (.lam A b) a) (subst 0 a' b')
  /-- **抽象：体平行归约；类型标注固定（与 `Step` 一致）。** -/
  | lam {A b b' : Term} : ParRedT E b b' → ParRedT E (.lam A b) (.lam A b')
  /-- **乘积：两部分同时归约。** -/
  | pi {A A' B B' : Term} :
      ParRedT E A A' → ParRedT E B B' → ParRedT E (.pi A B) (.pi A' B')
  /-- **局部定义：值与体同时归约，并执行替换。** -/
  | letE {A t t' b b' : Term} :
      ParRedT E t t' → ParRedT E b b' → ParRedT E (.letE A t b) (subst 0 t' b')

/-- **`ParRedT` 对**每个**项自反。**

**=> 一条构造子即可：`zero`。这与前两轮需要 `Rewritable` 谓词的困境形成对照，
说明 `zero` 正是缺失的那一块。** -/
theorem parRedT_refl (E : DefEnv) (t : Term) : ParRedT E t t :=
  ParRedT.zero t

/-- **`ParRedS` 可嵌入 `ParRedT`：去掉「必须替换」的约束后，旧构造子都还在。**

**=> 按构造子逐条翻译；`ParRedS` 的每条规则在 `ParRedT` 中都有对应。** -/
theorem parRedS_to_parRedT {E : DefEnv} {a b : Term} (h : ParRedS E a b) : ParRedT E a b := by
  induction h with
  | var n => exact ParRedT.zero _
  | sort k l => exact ParRedT.zero _
  | const c => exact ParRedT.zero _
  | delta c body he => exact ParRedT.delta c body he
  | app _ _ ihf iha => exact ParRedT.app ihf iha
  | beta _ _ ihb iha => exact ParRedT.beta ihb iha
  | lam _ ih => exact ParRedT.lam ih
  | pi _ _ ihA ihB => exact ParRedT.pi ihA ihB
  | letE _ _ iht ihb => exact ParRedT.letE iht ihb

end Lattice.Core.CIC
