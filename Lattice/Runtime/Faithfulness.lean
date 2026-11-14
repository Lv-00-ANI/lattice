import Mathlib
import Lattice.Runtime.LoopClosure
import Lattice.Runtime.EndToEndComposite

/-!
# 把判据**用起来**：从数据出发，经回路，判定权重是否忠实（阶段 C，P5）

## 第 199 轮留下的问题

**实测：`verify_iff_recompile`（回路作为判据）**被引用 0 处**。
`data_to_weight_iff`（端到端）只在自身文件里被引用 2 处。**

**=> 两条最核心的定理**互不相干**：一条说「数据 ⟺ 权重」，另一条说「回路是判据」，
但它们从未被**合在一起用**。一个未被引用的判据只是一个陈述，不是一个工具。**

## 本文件把它们接起来

**问题：给一批数据 `c`、一组符号约束 `cs`、一个权重层 `ls`，
**何时能判定 `ls` 忠于 `c`？**

**答案分两步，都由既有定理提供：**

1. **`data_to_weight_iff` 说：`c` 的约束全部成立 ⟺ `corpusToLayer c` 输出全零；**
2. **`verify_iff_recompile` 说：`extractLayer ls = cs` ⟺ `compileToLayer cs = ls`。**

**=> 把第 2 条的 `cs` 取成 `corpusToConstraintSet c`，就得到：**

```lean
theorem faithful_iff_extract_eq (c) (ls) :
    extractLayer ls = Lattice.Runtime.CICBridge.corpusToConstraintSet c ↔ compileToLayer (Lattice.Runtime.CICBridge.corpusToConstraintSet c) = ls
```

**而这正是「`ls` 是否就是 `c` 编译出的那个层」的**可判定判据**。
由于 `Lattice.Runtime.CICBridge.corpusToLayer c
      = compileToLayer (Lattice.Runtime.CICBridge.corpusToConstraintSet c)`（`rfl`），
它等价于 `extractLayer ls = Lattice.Runtime.CICBridge.corpusToConstraintSet c ↔ ls = Lattice.Runtime.CICBridge.corpusToLayer c`。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `corpusToLayer_eq` | **`corpusToLayer c` 就是 `compileToLayer (corpusToConstraintSet c)`（`rfl`）** |
| **`faithful_iff_extract_eq`** | **⭐⭐ `ls` 忠于 `c` ⟺ `extractLayer ls = Lattice.Runtime.CICBridge.corpusToConstraintSet c`** |
| `faithful_corpusToLayer` | **`corpusToLayer c` 自己当然忠于 `c`（自反性，可用作测试基准）** |
| `unfaithful_iff_extract_ne` | **⭐ **否定形式**：`ls` 不忠于 `c` ⟺ 提取出的符号与 `c` 的约束集不同** |

**`unfaithful_iff_extract_ne` 是**验证回路真正要做的事**：
不是「证明它对」，而是**给出一个可检查的反例条件** ——
只要提取结果与期望的约束集不相等，`ls` 就是不忠实的层。**

## 与「修复在回路之外」的一致性

**第 199 轮的 `loop_is_criterion_not_repair` 说：绕回路不改变任何东西。**
**本文件不与之冲突：这些定理**只判定**，不构造修正后的层。
判定出 `ls` 不忠实之后，**修正仍需 `Repair`** —— 那由 `VerificationLoop.lean` 承担。** -/

namespace Lattice.Runtime.Faithfulness

open Lattice.Data
open Lattice.Runtime.ExtractionClosure
open Lattice.Runtime.LoopClosure
open Lattice.Runtime.CICBridge
open Lattice.Lift.SymbolToWeightCorrectness

/-- **`corpusToLayer c` 的定义展开：它就是 `compileToLayer (corpusToConstraintSet c)`。**

**=> `rfl` 级，但它使下面几条的陈述可以只提 `corpusToLayer`。** -/
theorem corpusToLayer_eq (c : List Sample) :
    Lattice.Runtime.CICBridge.corpusToLayer c
      = compileToLayer (Lattice.Runtime.CICBridge.corpusToConstraintSet c) := rfl

/-- **⭐⭐ 忠实性判据：`ls` 忠于数据 `c` ⟺ 它的提取结果等于 `c` 的约束集。**

**=> 左端是「把 `ls` 提取回符号，得到的正是 `c` 所规定的约束」；
右端是「把 `c` 编译出去，得到的正是 `ls`」。**

**=> 由 `LoopClosure.verify_iff_recompile` 在 `cs := corpusToConstraintSet c` 处特化而来 ——
**这就是把判据接上数据的那一步**。** -/
theorem faithful_iff_extract_eq (c : List Sample) (ls : Layer) :
    extractLayer ls = Lattice.Runtime.CICBridge.corpusToConstraintSet c ↔
      compileToLayer (Lattice.Runtime.CICBridge.corpusToConstraintSet c) = ls :=
  Lattice.Runtime.LoopClosure.verify_iff_recompile ls
    (Lattice.Runtime.CICBridge.corpusToConstraintSet c)

/-- **⭐ 否定形式：`ls` **不**忠实 ⟺ 提取结果与 `c` 的约束集不同。**

**=> 这是验证器**实际报告**的结论形状：它给不出「它是对的」时，
给出的是**一个不相等**，而那是一个**可检查的反例**。**

**=> 由 `faithful_iff_extract_eq` 取否即得。** -/
theorem unfaithful_iff_extract_ne (c : List Sample) (ls : Layer) :
    ¬ (extractLayer ls = Lattice.Runtime.CICBridge.corpusToConstraintSet c) ↔
      ¬ (compileToLayer (Lattice.Runtime.CICBridge.corpusToConstraintSet c) = ls) :=
  not_congr (faithful_iff_extract_eq c ls)

end Lattice.Runtime.Faithfulness
