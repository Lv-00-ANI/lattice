import Mathlib
import Lattice.Runtime.CICToConstraint
import Lattice.Runtime.SymbolToWeightCorrectness

/-!
# 桥的第二段：`CIC → ConstraintSet → Layer`，闭环真正抵达符号模型（阶段 C，P4）

## 第一段回顾

**第 893 轮的 `cicToConstraint : Term → Option VectorConstraint` 把**单个** CIC 项译成一个线性约束，
并证了 `lam`/`pi`/`sort` 返回 `none`（函数与宇宙不是线性约束）。**

**=> 第一段只到「一个 term ↦ 一个约束」为止。闭环要抵达 CIC，还差两件事：**

1. **把一个 `Term` **列表**（或一个可递归的项）译成 `ConstraintSet`；**
2. **与既有的 `compileToLayer : ConstraintSet → Layer` 复合，并接上 `convertVec_preserves_semantics`。**

## 本文件做的两件事

### 一、列表版桥 `cicCtxToConstraintSet`

**`ConstraintSet = List VectorConstraint`，而一个 CIC 上下文 `CICCtx = List Term` 是一个项列表。
两者的**形状**本来就同构。**

**=> `cicCtxToConstraintSet` 把上下文里每个项译成约束，**过滤掉 `none` 的项**：
不可译的项不是「失败」，而是**它不贡献约束**（`lam`/`pi` 不是约束，本就不该产生一个）。**

### 二、闭环复合 `cic_loop_reaches_weight`

**把三段接起来：**

```
CIC 项列表  --cicCtxToConstraintSet-->  ConstraintSet
            --compileToLayer---------->  Layer
            --LayerOut = 0 ↔ Sat----->  权重侧的零化条件
```

**=> 这条定理的陈述是：对一个全部项都可译的 CIC 上下文 `ctx` 与赋值 `x`，
「`ctx` 里的约束全部成立」⟺「编译出的权重层对 `x` 的输出全部为零」。**

**它的证明只是 `cicCtxToConstraintSet_sat_iff` 与 `symbolToWeight_correct` 的复合 ——
**内容不在证明里，在**这条链被写下来**这件事里**：在此之前，
`Core/CIC` 与 `Lib/` 之间没有任何一条定理把它们连接起来。** -/

namespace Lattice.Runtime.CICBridge

open Lattice.Core.CIC
open Lattice.Lift.SymbolToWeightCorrectness

/-- **上下文版桥：把一个 CIC 上下文译成约束集。**

**=> `List.filterMap` 而不是 `map`：不可译的项被**丢弃**而不是失败。**
**理由是语义的：`lam`/`pi`/`sort` 不是约束，它们**不应该**产生约束；
让它们产生 `none` 再在列表里现形，等于把「不是约束」编码成「一个缺失的约束」。** -/
def cicCtxToConstraintSet (ctx : CICCtx) : List VectorConstraint :=
  ctx.filterMap cicToConstraint

/-- **空上下文译成空约束集。**

**=> 空约束集在所有赋值下都平凡满足，因此这条与 `AllSatisfied` 的定义是一致的。** -/
theorem cicCtxToConstraintSet_nil :
    cicCtxToConstraintSet [] = [] := rfl

/-- **只有 `const` 与 `var` 会对约束集有贡献。**

**=> 这是 `cicToConstraint_isSome_iff` 在列表上的像：
可译项的集合恰好是 `const`/`var` 的像。** -/
theorem cicCtxToConstraintSet_eq_filterMap (ctx : CICCtx) :
    cicCtxToConstraintSet ctx
      = ctx.filterMap (fun t => match t with
          | .const k => some ⟨[], -(k : Int)⟩
          | .var n => some ⟨List.replicate (n + 1) 0 |>.set n 1, 0⟩
          | _ => none) := rfl

/-- **可译性对上下文是**逐项**的。**

**=> 一个项进入约束集，当且仅当它是 `const` 或 `var`。**
**=> 这使「哪些 CIC 上下文能编译成权重」成为一个**可判定**的谓词，
而不是一个「大概能吧」的印象。** -/
theorem mem_cicCtxToConstraintSet_iff (ctx : CICCtx) (v : VectorConstraint) :
    v ∈ cicCtxToConstraintSet ctx ↔
      ∃ t ∈ ctx, cicToConstraint t = some v := by
  unfold cicCtxToConstraintSet
  rw [List.mem_filterMap]

/-- **桥的语义正确性：对于全部项都可译的上下文，约束集满足 ⟺ 每一项的约束都满足。**

**=> 这条把 `ConstraintSet` 的 `AllSatisfied` 拉回到 CIC 侧的逐项陈述。
它是第一段（单 term）在列表上的推广，也是与 `compileToLayer` 复合所需的唯一前提。** -/
theorem cicCtxToConstraintSet_sat_iff (ctx : CICCtx) (x : List Int) :
    (∀ v ∈ cicCtxToConstraintSet ctx, VectorConstraintSat v x) ↔
      ∀ t ∈ ctx, ∀ v, cicToConstraint t = some v → VectorConstraintSat v x := by
  unfold cicCtxToConstraintSet
  constructor
  · intro h t ht v hv
    exact h v (List.mem_filterMap.mpr ⟨t, ht, hv⟩)
  · intro h v hv
    obtain ⟨t, ht, htv⟩ := List.mem_filterMap.mp hv
    exact h t ht v htv

/-- **⭐ 闭环抵达符号模型：CIC 上下文的约束全部成立 ⟺ 编译出的权重层输出全部为零。**

**=> 这是本文件的核心交付。它把三段接起来：**

```
CIC 上下文  --cicCtxToConstraintSet-->  ConstraintSet
            --compileToLayer---------->  Layer
            --symbolToWeight_correct-->  权重侧零化
```

**左端是**符号模型**（CIC 的项），右端是**权重**（`LayerOut` 的零化条件）。**

**在此之前，`Core/CIC` 与 `Lib`/`Runtime` 的权重侧之间没有任何一条定理把它们连接起来 ——
第 892 轮实测：91 个 CIC 模块在 `Core` 之外只有 2 个消费者，其中没有一个是权重侧的。**
**=> 这条定理就是那个缺失的连接。** -/
theorem cic_loop_reaches_weight (ctx : CICCtx) (x : List Int) :
    (∀ t ∈ ctx, ∀ v, cicToConstraint t = some v → VectorConstraintSat v x) ↔
      AllZeroOutputs (compileToLayer (cicCtxToConstraintSet ctx)) x := by
  rw [← symbolToWeight_correct]
  exact (cicCtxToConstraintSet_sat_iff ctx x).symm

end Lattice.Runtime.CICBridge
