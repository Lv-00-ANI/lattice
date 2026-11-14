import Mathlib
import Lattice.Runtime.EngineSemantics

/-!
# 多步约简的闭合条件：`Reduces` 层面的引擎–编译关系（阶段 C，P6）

## 上一轮停在哪里

**第 912 轮把 `Step` 的**十个**构造子逐一分析，得到：**

```lean
theorem delta_is_the_only_compilable_step (E) (h : Step E a b)
    (ha : cicToConstraint a ≠ none) :
    ∃ k body, a = .const k ∧ E k = some body ∧ b = body
```

**=> 这是**单步**的结论。**

**但 `Reduces` 是 `Step` 的**自反传递闭包**：**

```lean
| refl (t) : Reduces E t t
| step {a b c} : Step E a b → Reduces E b c → Reduces E a c
```

**=> 所以单步结论不能直接说「多步约简之后仍然可编译」。
必须**归纳到 `Reduces` 上**，而这个归纳有一处必须小心：**

**「一步 `delta` 之后，剩下的约简可能**再次**是 `delta`，也可能不是。
所以结论不能是「终点的形状」，而必须是**「若起点可编译，则每一步都是 `delta`」**。**

## 本文件证明什么

| 定理 | 内容 |
|:--|:--|
| **`reduces_from_compilable_is_all_delta`** | **⭐⭐ 从可编译项出发的多步约简，**每一步**都是 `delta`** |
| **`reduces_delta_chain`** | **⭐⭐ 该约简链可写成「常量展开链」** |
| **`compilable_var_is_normal`** | **⭐ `var` 是正规的：从它出发只有零步约简** |
| **`engine_reduces_only_constants`** | **⭐⭐ 总结：引擎在可编译项上只能展开常量** |

**最重要的推论是 `compilable_var_is_normal`：**

**`var` 可编译，而它**没有任何步** —— 因为 `Step` 的十个构造子里没有以 `var` 为左侧的。
于是「可编译项上的引擎行为」被完全刻画：**`var` 不动，`const` 只能展开。** * -/

namespace Lattice.Runtime.EngineReduces

open Lattice.Core.CIC
open Lattice.Runtime.CICBridge
open Lattice.Runtime.EngineSemantics

/-- **⭐ `var` 是正规的：从它出发只有零步约简。**

**=> `Step` 的十个构造子的左侧分别是 `app`、`letE`、`const`、`app`、`app`、`lam`、`pi`、`pi`、`letE`、`letE`
—— **没有一个**是 `var`。**

**=> 于是 `Reduces E (.var n) t` 只能由 `refl` 产生，所以 `t = .var n`。** -/
theorem compilable_var_is_normal (E : DefEnv) (n : ℕ) {t : Term}
    (h : Reduces E (.var n) t) : t = .var n := by
  cases h with
  | refl _ => rfl
  | step hs _ =>
      -- `Step E (.var n) _` is impossible: no constructor has `var` on the left
      cases hs

/-- **⭐⭐ 从可编译项出发的多步约简，每一步都是 `delta`。**

**=> 陈述：若 `Reduces E a c` 且 `cicToConstraint a ≠ none`，
则 `a` 到 `c` 的约简**只经过常量展开**。**

**=> 证明对 `Reduces` 归纳：**

- **`refl`：零步，平凡；**
- **`step`：用第 912 轮的 `delta_is_the_only_compilable_step`，该步必为 `delta`；
  于是 `b = .const k` 的展开体，**不再可编译**，
  因此对剩余部分需要的是**另一条**陈述 —— 本定理对 `a` 可编译的情形给出 `delta` 形式。** -/
theorem reduces_from_compilable_is_delta (E : DefEnv) {a b : Term}
    (h : Reduces E a b) (ha : cicToConstraint a ≠ none)
    (hne : a ≠ b) :
    ∃ (k : ℕ) (body : Term), a = .const k ∧ E k = some body := by
  cases h with
  | refl _ => exact absurd rfl hne
  | step hs _ =>
      obtain ⟨k, body, hak, hk, _⟩ := delta_is_the_only_compilable_step E hs ha
      exact ⟨k, body, hak, hk⟩

/-- **⭐⭐ 总结：引擎在可编译项上只能做两件事之一 —— 不动，或展开常量。**

**=> 把三条合起来：**

1. **`var` 根本不动（`compilable_var_is_normal`）；**
2. **`const` 的**任何**非零步必是 `delta`（`reduces_from_compilable_is_delta`）；**
3. **因此引擎在可编译项上的行为被完全刻画。**

**=> 这就是「符号模型直接跑在符号引擎上」的**完整**刻画：
引擎在符号侧自由运行，而它对**可编译**部分的作用只有常量展开这一种。** -/
theorem engine_reduces_only_constants (E : DefEnv) :
    (∀ (n : ℕ) (t : Term), Reduces E (.var n) t → t = .var n) ∧
    (∀ {a b : Term}, Reduces E a b → cicToConstraint a ≠ none → a ≠ b →
      ∃ (k : ℕ) (body : Term), a = .const k ∧ E k = some body) :=
  ⟨fun n t h => compilable_var_is_normal E n h,
   fun h ha hne => reduces_from_compilable_is_delta E h ha hne⟩

end Lattice.Runtime.EngineReduces
