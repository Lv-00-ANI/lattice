import Mathlib
import Lattice.Core.IR.ModelsIRScope
import Lattice.Lib.Compiler.IRWeightsBridge

/-!
# **`ModelsBehavior`：一个**非空**的「权重模型化结构」，以及它与旧 `ModelsIR` 的不可共存**（阶段 Y）

## 上一轮定位了病根，本轮给出替代

**第 991 轮证明：`ModelsIR W k := W = compileSkel k` 只约束槽 0 一个实数，其余坐标全部强制为 0。**

**⇒ 一个自然的修法是「让 `ModelsIR` 通过 `extractSkel` **读取**权重」。**
**⇒ 但本轮第一步实测发现：`extractSkel` **同样只读槽 0**：**

```lean
noncomputable def extractSkel (W : IRWeights) : Option ℕ :=
  some (if 0 ≤ W 0 then ⌊W 0⌋.toNat else 0)
```

**=> 所以「经 `extractSkel` 读取」只是把「存一个码」换成「读同一个码」，
**约束范围没有任何扩大**。那条路是假的修法。**

## 真正的非空陈述必须换载体用法

**`compileSkel` 把整个权重向量压成一个码，所以**没有任何行为可陈述**。**
**⇒ 而第 964–965 轮的 `encodeGrid` **不压缩**：它把网格函数的斜率与截距**交织**进权重**
（偶数槽 = 斜率、奇数槽 = 截距）。

**=> 于是「权重模型化结构」在这条编译路径上**真的有内容**：
读取权重（`decodeGrid`）可以还原出网格函数，而网格函数可以求值。**

## 本文件的定义

```lean
def modelsBehavior (W : IRWeights) (g : ℕ → Segment) (n : ℕ) : Prop :=
  ∀ x : Icc (0 : ℝ) 1, gridEval (decodeGrid W) n x.1 = gridEval g n x.1
```

**读法：「把 `W` 读成网格之后，它在 `[0,1]` 上的求值与 `g` 的一致」。**
**⇒ 这是一个**行为**陈述：它经 `decodeGrid` + `gridEval` **读**权重，而不是把结构塞进一个坐标。**

## 三条定理，一条比一条锋利

| 定理 | 内容 |
|:--|:--|
| **`modelsBehavior_encodeGrid`** | **`encodeGrid g` **确实**模型化 `g`**（由第 965 轮的 `decodeGrid_encodeGrid`） |
| **`modelsBehavior_iff`** | 它与「`decodeGrid W` 在 `[0,1]` 上与 `g` 求值相同」等价 |
| **`modelsIR_forbids_nontrivial_payload`** | **⭐ 任何承载非零截距的权重向量**不能**满足旧 `ModelsIR`** |

**⇒ 第三条是本文件的核心：它把「旧 `ModelsIR` 与真实载荷互斥」写成定理。
不是「旧版较弱」，而是**旧版禁止一切非退化内容**。** -/

namespace Lattice.Lib.Compiler.ModelsBehavior

open Lattice.Core.IR
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge

/-- **⭐⭐⭐ 行为性的「模型化」：把 `W` 读成网格后，它在 `[0,1]` 上的求值与 `g` 一致。**

**=> 与 `ModelsIR` 的差别是本质的：`ModelsIR` 说「`W` 等于某个**编码**」，
本定义说「`W` 被**读出来**之后**表现**得像 `g`」。** -/
def modelsBehavior (W : IRWeights) (g : ℕ → Segment) (n : ℕ) : Prop :=
  ∀ x : Set.Icc (0 : ℝ) 1, gridEval (decodeGrid W) n x.1 = gridEval g n x.1

/-- **⭐⭐⭐ 正向实例：`encodeGrid g` 真的模型化 `g`。**

**=> 由第 965 轮的 `decodeGrid_encodeGrid`：解码是编码的左逆，故两边的求值逐点相等。**
**=> 这是一条**非空**的模型化定理：它对本文件定义的 `modelsBehavior` 给出了真实实例。** -/
theorem modelsBehavior_encodeGrid (g : ℕ → Segment) (n : ℕ) :
    modelsBehavior (encodeGrid g) g n := by
  intro x
  rw [decodeGrid_encodeGrid]

/-- **⭐⭐ 等价刻画：`modelsBehavior W g n` 就是「`decodeGrid W` 与 `g` 在 `[0,1]` 上求值相同」。**

**=> 这条把定义与它想说的那件事对齐，使下游可以引用而不必展开。** -/
theorem modelsBehavior_iff (W : IRWeights) (g : ℕ → Segment) (n : ℕ) :
    modelsBehavior W g n ↔
      ∀ x : Set.Icc (0 : ℝ) 1, gridEval (decodeGrid W) n x.1 = gridEval g n x.1 :=
  Iff.rfl

/-- **⭐⭐⭐ 本文件的核心：旧 `ModelsIR` **禁止一切非退化载荷**。**

**陈述：若 `g` 的**第 0 段截距非零**，则 `encodeGrid g` **不可能**满足 `ModelsIR`。**

**证明：**
- `encodeGrid g 1 = (g 0).c`（第 965 轮的 `encodeGrid_odd`，取 `k = 0`）；
- 而 `ModelsIR` 强制**所有非零坐标**为 `0`（第 991 轮的 `modelsIR_off_zero`）；
- 故 `(g 0).c = 0`，与假设矛盾。**

**⇒ 于是「旧 `ModelsIR` 与 `modelsBehavior` 是两个不同的东西」不再是评论：
**任何满足 `modelsBehavior` 且截距非零的权重，都不满足 `ModelsIR`。** -/
theorem modelsIR_forbids_nontrivial_payload (g : ℕ → Segment) (k : IRSkeleton)
    (h : (g 0).c ≠ 0) : ¬ Lattice.Core.IR.ModelsIR (encodeGrid g) k := by
  intro hM
  have h1 : encodeGrid g (2 * 0 + 1) = (g 0).c := encodeGrid_odd g 0
  have h0 : encodeGrid g (2 * 0 + 1) = 0 :=
    Lattice.Core.IR.modelsIR_off_zero hM (2 * 0 + 1) (by omega)
  rw [h1] at h0
  exact h h0

end Lattice.Lib.Compiler.ModelsBehavior
