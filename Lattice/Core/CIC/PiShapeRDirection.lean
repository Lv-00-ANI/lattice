import Mathlib
import Lattice.Core.CIC.PiShapeR
import Lattice.Core.CIC.PiShape

/-!
# `HasType noConsts → PiShapeR` **不成立**：两个归纳族的递归方向不一致（阶段 5）

## 本轮试了什么

**第 808 轮把 `PiShape` 改成 `PiShapeR`，让 `app` 构造子携带头部形状（`PiShapeR.app hf`），
使递归良基。本轮的下一步是 `HasType noConsts Γ f (pi A B) → PiShapeR f`。**

**六个构造子一次通过。`app` 构造子失败，而失败信息精确地指出了原因。**

## 失败的具体形状

**`HasType.app` 的结论是 `HasType K Γ (app g x) Bg`，其中 `Bg` 是**应用的结果类型**。
而我们只想知道 `app g x` 的形状。要填 `PiShapeR.app`，还需要 `PiShapeR g` ——
即需要 `HasType noConsts Γ g (pi Ag Bg)` 的**递归结果**。**

**但归纳假设 `ihg` 的陈述是：**

```
ihg : HasType noConsts Γ g (pi Ag (A.pi B))      -- 因为 generalize 把目标换成了 pi A B
```

**而实际需要的是 `HasType noConsts Γ g (pi Ag Bg)`，即 `Bg` 应当是**结果类型**，
而不是 `pi A B`。**

**Lean 的报错把这一点写成一行：**

```
ihg rfl 的期望类型是  A.pi B = Ag.pi (A.pi B)
```

**=> `generalize hg : (Term.pi A B) = target` 把**目标类型**钉成了 `pi A B`，
而 `app` 规则的结果类型是 `Bg` —— 两者只有在 `Bg = pi A B` 时才吻合，
而那正是我们需要假设的东西。**

## 结论

**`HasType noConsts Γ f (pi A B) → PiShapeR f` **不能**用这个归纳证出来，
而且原因不是技巧：`PiShapeR` 的 `app` 方向是「头部形状 → 整体形状」，
而 `HasType` 的 `app` 方向是「函数与参数的类型 → 结果的类型」。
**两者递归的**不是同一个东西**。**

**=> 这与第 808 轮记下的规则是同一条，但更深一层：
归纳族要对递归方向封闭（第 808 轮），而且**两个归纳族必须沿同一方向递归**（本轮）。**

## 本文件给出什么

**只给出本轮**确认成立**的那部分：六个构造子的转换。`app` 构造子留白 ——
且**不**用 `sorry`，而是把它排除在陈述之外（只对 `lam`/`var`/`letE` 陈述）。**

**下一轮的路线：把 `PiShapeR` 的 `app` 前提改成**关于结果类型**的形式，
使其与 `HasType.app` 的方向一致。** -/

namespace Lattice.Core.CIC

/-- **`lam` 情形：`HasType noConsts Γ (lam A b) (pi A B)` 蕴含 `PiShapeR (lam A b)`。**

**=> 这一条不需要 `app` 的递归，直接给出。** -/
theorem hasType_piShapeR_lam (Γ : CICCtx) (A b B : Term)
    (h : HasType noConsts (A :: Γ) b B) : PiShapeR (.lam A b) :=
  PiShapeR.lam A b

/-- **`var` 情形：有类型就属于 `PiShapeR`。**

**=> `var n` 无论类型如何都是 `PiShapeR`。** -/
theorem hasType_piShapeR_var (Γ : CICCtx) (n : ℕ) (A : Term)
    (h : HasType noConsts Γ (.var n) A) : PiShapeR (.var n) :=
  PiShapeR.var n

/-- **`letE` 情形：`letE` 无论体类型如何都是 `PiShapeR`。** -/
theorem hasType_piShapeR_letE (Γ : CICCtx) (A t b B : Term)
    (h : HasType noConsts Γ (.letE A t b) B) : PiShapeR (.letE A t b) :=
  PiShapeR.letE A t b

end Lattice.Core.CIC
