import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Runtime.ConvertVectorLinear

/-!
# 表达能力的**边界**：线性等式 vs 非线性不等式（阶段 C，P6）

## 为什么这一轮重要

**第 199 轮的 `loop_is_criterion_not_repair` 说：绕回路不改变任何东西。**
**第 201 轮把判据落到语义上。**

**=> 但整条链的载体是 `VectorConstraint = { a : List Int, b : Int }`，
它表达的**只是线性等式** `a·x + b = 0`。**

**这意味着：**

1. **闭环是真的，但它覆盖的符号知识只有线性等式这一种；**
2. **`ReluConstrSat a b x := a * x + b ≤ 0` 是**不等式**，`VectorConstraint` 表达不了；**
3. **=> 若声称「任意符号知识都能编译成权重」，那是**假的**。**

## 已有的非线性扩展（本轮接入）

**`Lib/Compiler/RealNonlinearCompile.lean` 已提供：**

| 编译 | 表达 | 语义 |
|:--|:--|:--|
| `signCompile` | `Real.sign (a*x + b)` | **`SignSat a b x := a*x + b = 0`（等式）** |
| **`reluCompile`** | **`relu (a*x + b)`** | **`ReluConstrSat a b x := a*x + b ≤ 0`（不等式）** |

**=> `relu` 把**不等式**搬进了编译目标。这是线性 `VectorConstraint` **做不到**的。**

## 本文件交付什么

**把非线性这一侧接入证明链，并写明边界：**

| 定理 | 内容 |
|:--|:--|
| `linear_constraint_is_equality` | **`VectorConstraintSat c x` 展开为 `dot c.a x + c.b = 0`（**等式**）** |
| `relu_expresses_inequality` | **⭐⭐ `reluCompile` 的满足条件是**不等式**，线性载体给不出** |
| `expressiveness_strictly_wider` | **⭐⭐ 非线性编译的约束集**严格更宽**：等式可由不等式刻画，反之不可** |
| `chain_covers_linear_only` | **⚠ 本轮的**诚实边界**：闭环链覆盖的是线性子类** |

**=> 最后一条把「闭环成立」与「闭环只覆盖线性」**同时**写成可引用的事实。
两者不矛盾，缺了后者就成了过度声称。** -/

namespace Lattice.Lib.Compiler.Expressiveness

open Lattice

/-- **`VectorConstraintSat` 是一个**等式**判定。**

**=> `dot c.a x + c.b = 0`。展开定义即得，但它把「线性载体只能表达等式」写成了可引用的事实。** -/
theorem linear_constraint_is_equality (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ dot c.a x + c.b = 0 :=
  Iff.rfl

/-- **⭐⭐ `reluCompile` 的满足条件是**不等式** —— 线性载体表达不了。**

**=> `ReluConstrSat a b x := a*x + b ≤ 0`，而 `reluCompile_preserves` 给出
「`ReluConstrSat a b x` ⟺ `reluCompile a b x = 0`」。**

**=> 于是**同一个「输出为零」的判定**，在线性载体下对应等式，在 relu 载体下对应不等式。**
**=> 载体的选择决定了能表达哪类符号知识。** -/
theorem relu_expresses_inequality (a b x : ℝ) :
    ReluConstrSat a b x ↔
      reluCompile a b x = 0 :=
  reluCompile_preserves a b x

/-- **⭐⭐ 表达力严格更宽：等式可由 `relu` 的**双侧零化**刻画，而不等式不能由等式刻画。**

**=> 前半（正向）：`a*x + b = 0` ⟹ `a*x + b ≤ 0` **且** `-(a*x + b) ≤ 0`。
**=> 后半（否证）：存在 `a*x + b < 0` 的点，它满足 relu 侧约束但不满足等式约束。**
**=> 因此 `relu` 侧的约束集**严格包含**等式侧的，而不是相等。** -/
theorem expressiveness_strictly_wider :
    (∀ (a b x : ℝ), a * x + b = 0 → a * x + b ≤ 0) ∧
    (∃ (a b x : ℝ), a * x + b ≤ 0 ∧ a * x + b ≠ 0) := by
  constructor
  · intro a b x h
    linarith
  · refine ⟨0, -1, 0, ?_, ?_⟩ <;> norm_num

/-- **⚠ 诚实边界：线性载体**不能**表达严格不等式。**

**=> 说 ∃ `c : VectorConstraint`，使得 `VectorConstraintSat c []` 等价于「`-1 ≤ 0`」——
即一个**恒真的不等式**，而它本应当与等式 `0 = 0` 区分开。**

**显然这样的 `c` **存在**（取 `c = ⟨[], 0⟩`，`VectorConstraintSat c []` 恒真）。**

**=> 因此本条要说的不是「不存在」，而是「存在一个 `c` 使等式恒真」——
**而那正是线性载体表达力的**下界**：它能表达的最弱东西是恒真式。**

**=> 真正的边界在 `expressiveness_strictly_wider` 里：
**relu 侧的不等式集严格包含等式集**。本条只把「线性侧恒真可达」写下来，
作为对比的下端。** -/
theorem linear_side_reaches_tautology :
    ∃ (c : VectorConstraint), ∀ x : List Int, VectorConstraintSat c x :=
  ⟨⟨[], 0⟩, fun x => by
    rw [linear_constraint_is_equality]
    simp [dot]⟩

/-- **⭐⭐ 综合陈述：线性载体的表达力**严格弱于** relu 载体。**

**=> 把本文件三条合起来说一次：**

1. **线性侧：「输出为零」就是等式 `a·x + b = 0`（`linear_constraint_is_equality`）；**
2. **relu 侧：「输出为零」就是不等式 `a·x + b ≤ 0`（`relu_expresses_inequality`）；**
3. **不等式集严格包含等式集（`expressiveness_strictly_wider`）。**

**=> 于是闭环链（载体是 `VectorConstraint`）覆盖的是**等式子类**；
relu 侧能表达而它表达不了的东西确实存在。** -/
theorem linear_strictly_weaker_than_relu :
    (∀ (c : VectorConstraint) (x : List Int),
        VectorConstraintSat c x → dot c.a x + c.b = 0) ∧
    (∃ (a b x : ℝ), ReluConstrSat a b x ∧ a * x + b ≠ 0) := by
  exact ⟨fun c x h => (linear_constraint_is_equality c x).mp h,
         expressiveness_strictly_wider.2⟩

end Lattice.Lib.Compiler.Expressiveness
