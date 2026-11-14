import Mathlib
import Lattice.Runtime.Faithfulness

/-!
# 判据的**语义落点**：等式检查与行为满足是同一件事（阶段 C，P5）

## 第 200 轮的判据缺一个落点

**第 200 轮的 `faithful_iff_extract_eq` 是一条**等式**判据：**

```lean
extractLayer ls = corpusToConstraintSet c  ↔  compileToLayer (corpusToConstraintSet c) = ls
```

**=> 它说的是「提取出的符号与期望的符号集**逐项相等**」。**
**但它没有说「这个层在**行为上**是否满足那组约束」。**

**这是验证器真正要回答的问题：**

> **给定层 `ls` 与赋值 `x`，`ls` 是否让那组约束**成立**？**

**=> 等式相等是**语法**判据，`AllSatisfied` 是**语义**判据。
两者之间的桥**此前不存在**（实测：无任何 `AllSatisfied`/`extractLayer` 关联定理）。**

## 本文件建这座桥

**`compileToLayer cs` 的输出，在 `x` 处为零 ⟺ `cs` 在 `x` 处全部成立。**

**这就是既有的 `symbolToWeight_correct`。而 `corpusToLayer c = compileToLayer (corpusToConstraintSet c)`
（`rfl`），于是：**

```lean
theorem faithful_semantics (c) (x) :
    AllZeroOutputs (Lattice.Runtime.CICBridge.corpusToLayer c) x ↔
      AllSatisfied (Lattice.Runtime.CICBridge.corpusToConstraintSet c) x
```

**=> 这是把第 200 轮的语法判据**接到**语义上的那一步。**

## 于是验证器有两个可用的判据

| 判据 | 形状 | 用途 |
|:--|:--|:--|
| `faithful_iff_extract_eq` | **`extractLayer ls = corpusToConstraintSet c`** | **语法：逐项相同** |
| **`satisfies_iff_extractLayer`** | **`AllSatisfied (extractLayer ls) x`** | **语义：行为满足** |

**=> 第二行是本文件的交付：**若 `ls` 提取出的约束在 `x` 处全部成立，
那么 `ls` 本身在 `x` 处的输出全部为零。**

**这把「提取」从「拿回符号」升级成「拿回**可用作验证的**符号」。** -/

namespace Lattice.Runtime.SemanticFaithfulness

open Lattice.Data
open Lattice.Data.Encode
open Lattice.Runtime.ExtractionClosure
open Lattice.Runtime.CICBridge
open Lattice.Runtime.Faithfulness
open Lattice.Lift.SymbolToWeightCorrectness

/-- **⭐ 语义落点：`corpusToLayer c` 在 `x` 处全零 ⟺ `c` 的约束集在 `x` 处全部成立。**

**=> 由 `symbolToWeight_correct` 在 `cs := corpusToConstraintSet c` 处特化，
再用 `corpusToLayer_eq`（`rfl`）换名。**

**=> 它把「数据 → CIC → 约束 → 权重」这条链的**语义**端固定下来：
右端是符号侧的满足判定，左端是权重侧的零化判定。** -/
theorem faithful_semantics (c : List Sample) (x : List Int) :
    AllZeroOutputs (corpusToLayer c) x ↔ AllSatisfied (corpusToConstraintSet c) x := by
  unfold Lattice.Runtime.CICBridge.corpusToLayer
  exact (symbolToWeight_correct (Lattice.Runtime.CICBridge.corpusToConstraintSet c) x).symm

/-- **⭐⭐ 提取出的符号**可用作验证**：若 `extractLayer ls` 在 `x` 处全部成立，
则 `ls` 在 `x` 处输出全零。**

**=> 这是验证器的核心推理步骤：**
**「我把 `ls` 提取成符号，那些符号在 `x` 处成立，所以 `ls` 在 `x` 处满足约束」。**

**=> 没有这条，提取只是一次格式转换；有了它，提取**产出了判据**。** -/
theorem satisfies_iff_extractLayer (ls : Layer) (x : List Int) :
    AllSatisfied (Lattice.Runtime.LoopClosure.extractLayer ls) x ↔
      AllZeroOutputs (compileToLayer (Lattice.Runtime.LoopClosure.extractLayer ls)) x :=
  symbolToWeight_correct (Lattice.Runtime.LoopClosure.extractLayer ls) x

/-- **⭐⭐ 更强：提取后重新编译，语义不变。**

**=> 因为 `compileToLayer (extractLayer ls) = ls`（第 199 轮的 `compile_extract_layer`），
所以「`extractLayer ls` 在 `x` 处成立」**直接等于**「`ls` 在 `x` 处输出全零」。**

**=> 这条把回路恒等与语义判据合成一条：**验证 `ls` 只需验证它的提取物，
而提取物重新编译回 `ls` 本身，因此两者是同一个判定。** -/
theorem satisfies_extractLayer_iff_self (ls : Layer) (x : List Int) :
    AllSatisfied (Lattice.Runtime.LoopClosure.extractLayer ls) x ↔ AllZeroOutputs ls x := by
  rw [satisfies_iff_extractLayer, Lattice.Runtime.LoopClosure.compile_extract_layer]

end Lattice.Runtime.SemanticFaithfulness
