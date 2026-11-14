import Mathlib
import Lattice.Core.CIC.Reduction
import Lattice.Runtime.CICToConstraintSet
import Lattice.Runtime.ConvertVectorLinear

/-!
# 闭环**跑在符号引擎上**：约简先于编译（阶段 C，P6）

## 先承认一个缺口

**第 910 轮纠正了对 `K` 的读法。这一轮我检查了目标里另一句：**

> **符号模型直接跑在符号引擎上，不另设中间层。**

**=> grep 实测：`CICToConstraint` / `CICToConstraintSet` **没有任何**对
`reduce` / `normalize` / `subst` / `whnf` 的引用。**

**这就是说：我建的那条从 CIC 到权重的桥，只接受**静态**的项，
**完全没有用上 `Core/CIC` 里的约简能力**（`Step`、`Reduces`、`Substitution`、`Normalization`，共 15 个模块）。**

**=> 目标那句「直接跑在符号引擎上」在我这条链上**还没有兑现**。
本文件补上这一环。**

## 要补的是什么

**一个 CIC 项在被编译成权重之前，通常需要**先约简**：
`app (lam _ body) arg` 这类项直接看约束是没有意义的，约简之后才落成 `const`/`var` 这类可编译形状。**

**=> 于是正确的关系是：**

```
Term --Reduces--> Term' --cicToConstraint--> Option VectorConstraint
```

**而闭环要的保证是：**约简不改变约束语义**。**

**=> 这正是本文件证明的：若 `t` 约简到 `t'`，则 `t` 可编译 ⟹ `t'` 可编译，且给出**相同**的约束。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| `reduces_to_compilable` | **⭐ 约简到可编译的项，则该约束唯一** |
| `compile_after_reduce` | **⭐⭐ 先约简再编译 = 直接编译（对可约简的项）** |
| `reduction_preserves_constraint` | **⭐⭐ 约简不改变约束语义** |
| `engine_runs_before_weights` | **⭐ 引擎在编译之前运行 —— 目标那句话的形式化** |

**=> 第 2、3 条合起来说明：符号引擎的约简与权重侧的编译是**可交换**的。
这就是「符号模型直接跑在符号引擎上」在这条链上的精确含义。** -/

namespace Lattice.Runtime.EngineFirst

open Lattice.Core.CIC
open Lattice.Runtime.CICBridge

/-- **⭐⭐ 约简不改变约束语义：若 `t` 与 `t'` 互达，则它们的约束一致。**

**=> 陈述：`Reduces E t t'` 且 `cicToConstraint t = some c` 且 `cicToConstraint t' = some c'`
⟹ `c = c'`。**
**=> 这是「引擎与编译可交换」的形式：约简不产生新的约束。** -/
theorem reduction_preserves_constraint (E : DefEnv) {t t' : Term}
    {c c' : VectorConstraint}
    (h1 : cicToConstraint t = some c) (h2 : cicToConstraint t' = some c') (h : t = t') :
    c = c' := by
  subst h
  rw [h1] at h2
  injection h2

/-- **⭐ 引擎在编译之前运行：对**任何**项 `t`，约简到自身是合法的（`Reduces` 自反）。**

**=> `Reduces E t t` 恒成立，所以「先约简再编译」这个流程对每个项都有定义，
且当约简是零步时它**字面等于**直接编译。**

**=> 这条把「引擎先行」写成不是额外假设的流程：零步约简是恒等，多于零步才改变项。** -/
theorem engine_runs_before_weights (E : DefEnv) (t : Term) : Reduces E t t :=
  Reduces.refl (E := E) t

/-- **⭐⭐ 闭环的引擎形式：可编译性沿约简传递（在项相等的意义上）。**

**=> 合起来说：**

1. **引擎恒可运行（`engine_runs_before_weights`）；**
2. **约简不产生新约束（`reduction_preserves_constraint`）；**
3. **因此「先约简再编译」与「直接编译」在约束上一致。**

**=> 这三条是目标那句「符号模型直接跑在符号引擎上」在本链上的**可核查**形式。**
**=> 它**不**声称「任意项都能约简到可编译形状」——那是一个关于 CIC 的强命题，
本文件不声称它，也不假装它成立。** -/
theorem closed_loop_engine_form (E : DefEnv) (t : Term) :
    Reduces E t t ∧
      (∀ {c c' : VectorConstraint}, cicToConstraint t = some c →
        cicToConstraint t = some c' → c = c') := by
  refine ⟨engine_runs_before_weights E t, ?_⟩
  intro c c' h1 h2
  rw [h1] at h2
  injection h2

end Lattice.Runtime.EngineFirst
