import Mathlib
import Lattice.Core.CIC.ParallelReductionZero

/-!
# `ParRedU`：补上 `letE` 的**非替换**构造子（阶段 5，`Step → ParRed` 的最后一块）

## 本轮先做的核实

**`Step → ParRedT` 的十情形归纳里，九条一次通过：**

| `Step` 构造子 | `ParRedT` 对应 |
|:--|:--|
| `beta` | **`ParRedT.beta (zero) (zero)`** |
| `zeta` | **`ParRedT.letE (zero) (zero)`** |
| `delta` | **`ParRedT.delta`** |
| `appL` / `appR` | **`ParRedT.app` 配 `zero`** |
| `lamBody` | **`ParRedT.lam`** |
| `piDom` / `piCod` | **`ParRedT.pi` 配 `zero`** |
| **`letVal` / `letBody`** | **无对应 —— `ParRedT.letE` **总是**替换** |

## 为什么 `letVal`/`letBody` 表达不出来

**`Step.letVal` 说 `letE A t b → letE A t' b`：值归约，**不**执行替换。**
**而 `ParRedT.letE` 的结论是 `subst 0 t' b'` —— 它**一定**替换。**

**=> 与第 820 轮 `letE` 不能自反是**同一个**缺陷：`letE` 只有「替换」一种形态，
没有「只归约内部」的形态。**

**`app`/`lam`/`pi` 都不需要补，因为它们的分支已经能表达内部归约
（`ParRedT.app (ParRedT.lam h) (zero a)` 就是 `appL`）。**
**=> `letE` 是唯一缺的。**

## 修正：`ParRedU`

**在 `ParRedT` 基础上补三条 `letE` 构造子：**

```lean
| letL {A t t' b} : ParRedU t t' -> ParRedU (letE A t b) (letE A t' b)      -- 值内部
| letR {A t b b'} : ParRedU b b' -> ParRedU (letE A t b) (letE A t b')      -- 体内部
| letE {A t t' b b'} : ParRedU t t' -> ParRedU b b' -> ParRedU (letE A t b) (subst 0 t' b')
```

**=> `letL`/`letR` 与 `Step.letVal`/`letBody` 一一对应；`letE` 对应 `Step.zeta`。
三条合起来覆盖 `Step` 关于 `letE` 的全部行为。** -/

namespace Lattice.Core.CIC

/-- **带 `letE` 内部归约的平行归约。**

**=> 与 `ParRedT` 的差别只有 `letL`/`letR` 两条：它们让 `letE` 能只归约值或体而不替换。
这是 `Step.letVal`/`letBody` 的对应物。** -/
inductive ParRedU (E : DefEnv) : Term → Term → Prop
  /-- **零处归约。** -/
  | zero (t : Term) : ParRedU E t t
  /-- **常量按 `delta` 展开。** -/
  | delta (c : ℕ) (body : Term) : E c = some body → ParRedU E (.const c) body
  /-- **应用：两边同时平行归约。** -/
  | app {f f' a a' : Term} : ParRedU E f f' → ParRedU E a a' → ParRedU E (.app f a) (.app f' a')
  /-- **β：体与参数同时归约，并执行替换。** -/
  | beta {A b b' a a' : Term} :
      ParRedU E b b' → ParRedU E a a' → ParRedU E (.app (.lam A b) a) (subst 0 a' b')
  /-- **抽象：体平行归约。** -/
  | lam {A b b' : Term} : ParRedU E b b' → ParRedU E (.lam A b) (.lam A b')
  /-- **乘积：两部分同时归约。** -/
  | pi {A A' B B' : Term} :
      ParRedU E A A' → ParRedU E B B' → ParRedU E (.pi A B) (.pi A' B')
  /-- **局部定义：只归约**值**，不替换。**

  **=> 与 `Step.letVal` 对应。** -/
  | letL {A t t' b : Term} : ParRedU E t t' → ParRedU E (.letE A t b) (.letE A t' b)
  /-- **局部定义：只归约**体**，不替换。**

  **=> 与 `Step.letBody` 对应。** -/
  | letR {A t b b' : Term} : ParRedU E b b' → ParRedU E (.letE A t b) (.letE A t b')
  /-- **局部定义：值与体同时归约，并执行替换。**

  **=> 与 `Step.zeta` 对应。** -/
  | letE {A t t' b b' : Term} :
      ParRedU E t t' → ParRedU E b b' → ParRedU E (.letE A t b) (subst 0 t' b')

/-- **`ParRedU` 对每个项自反。** -/
theorem parRedU_refl (E : DefEnv) (t : Term) : ParRedU E t t :=
  ParRedU.zero t

end Lattice.Core.CIC
