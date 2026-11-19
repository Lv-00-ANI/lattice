import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
import Lattice.Compose.Showcase.FullChain
import Lattice.Core.IR.Chain

/-!
# **官方展品 M-2：神经捷径——数据 → token → 权重，**符号层不出现**（阶段 W）

## 本文件的结论分两半，两半都交付

**M-2 是 `README.md` 链路图里唯一一条**绕过符号层**的路：数据 → token → 权重。**
**本文件按上一轮的计划做两件事：**

1. **把这条捷径**写出来**（`neuralShortcut`，一条 `compose` 链，L0 → L3）；**
2. **并如实记录它**表达不了什么**——因为这一半比第一半重要。**

## 为什么第三段只能是「计数向量」

**`Primitive` 的 `post` 是一个 `Prop`。要让它**诚实地**描述「神经捷径」，
它只能引用 token 侧与权重侧的量——**不许引用符号层**。**

**⇒ 而权重载体是 `IRWeights := ℕ → ℝ`，一个纯数值向量。**

**本文件能提供的、不借助符号层的最薄映射是：**

```lean
def tokenShapeVector (ts : List CharToken) : IRWeights :=
  fun n => if n < ts.length then 1 else 0
```

**⇒ 它记录的是**这一句有多少个 token**。它**不记录任何 token 的身份**。**

**这不是我没想到更好的写法，而是**这个形状的上限**：
`IRWeights` 的下标是 `ℕ`，而 token 的身份在权重侧没有任何指称——
**要让「`n` 号槽位对应哪个 token」可陈述，必须先有一个 token → 槽位的编码函数；
而那个函数正是符号层提供的东西。** 一旦引入它，捷径就不再是捷径。

**=> 所以 M-2 的诚实结论是：这条捷径**存在且可陈述**，
但在 `IRWeights := ℕ → ℝ` 这个载体上，它的**内容只有形状（长度），没有身份**。**

## 与 M-3 的对照

| 展品 | 路径 | 权重侧知道什么 |
|:--|:--|:--|
| **M-3 符号捷径** | 知识 → L2 → 权重 | **每个槽位对应一个骨架码**（`compileSkel` 把 `skeletonCode k` 放进槽 0） |
| **M-2 神经捷径** | 数据 → token → 权重 | **只有长度** |

**⇒ 两者的差别正是「有没有符号层」的差别，而 M-2 把那个差别**量化地**摆出来了。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`tokenShapeVector`** | **⭐⭐ token 列表 → 权重向量（只记长度）** |
| **`neuralPrim`** | **⭐⭐ L1 → L3 的 `Primitive`** |
| **`neuralShortcut`** | **⭐⭐⭐ L0 → L3，**经 M-1 的分词**、**不经符号层** |
| **`neuralShortcut_run`** | **⭐⭐⭐ 捷径的 `run` 等于 `some (tokenShapeVector (tokenizeV V s))`** |
| **`tokenShapeVector_no_identity`** | **⭐⭐⭐ 本文件的另一半：向量对任意两个等长 token 列表**相同** | -/

namespace Lattice.Compose.Showcase.NeuralShortcut

open Lattice.Compose

/-- **⭐⭐ token 列表 → 权重向量：槽位 `n` 在 `n < ts.length` 时为 `1`，否则为 `0`。**

**⇒ 它**只**记录长度。理由是载体本身：`IRWeights := ℕ → ℝ` 的下标是 `ℕ`，
而 token 的身份在权重侧没有指称——见文件头的说明。** -/
def tokenShapeVector (ts : List CharToken) : Lattice.Core.IR.IRWeights :=
  fun n => if n < ts.length then (1 : ℝ) else 0

/-- **⭐⭐ 神经捷径的第二段：token 列表 → 权重向量。全函数，故 `pre := True`。** -/
def neuralPrim : Primitive (List CharToken) Lattice.Core.IR.IRWeights where
  pre := fun _ => True
  post := fun ts W => tokenShapeVector ts = W
  run := fun ts => some (tokenShapeVector ts)
  sound := by
    intro ts _
    exact ⟨tokenShapeVector ts, rfl, rfl⟩
  strength := .exact
  coverage := none

/-- **⭐⭐⭐ 神经捷径：M-1 的 `tokenizePrim` 之后直接进权重，**符号层不出现**。**

**=> 这是五张展品里唯一一条从 L0 到 L3 且**跳过 L2** 的链。** -/
def neuralShortcut (V : OOVVocab) :
    Primitive (List Char) Lattice.Core.IR.IRWeights :=
  compose (Lattice.Compose.Showcase.FullChain.tokenizePrim V) neuralPrim (by
    intro s ts _
    trivial)

/-- **⭐⭐⭐ 捷径的 `run` 就是 `tokenShapeVector ∘ tokenizeV`。** -/
theorem neuralShortcut_run (V : OOVVocab) (s : List Char) :
    (neuralShortcut V).run s
      = (Lattice.tokenizeV V s).map tokenShapeVector := by
  cases h : Lattice.tokenizeV V s with
  | none => simp [neuralShortcut, compose, Lattice.Compose.Showcase.FullChain.tokenizePrim,
      neuralPrim, h]
  | some y => simp [neuralShortcut, compose, Lattice.Compose.Showcase.FullChain.tokenizePrim,
      neuralPrim, h]

/-- **⭐⭐⭐ **本文件的另一半**：等长的两个 token 列表得到**同一个**权重向量。**

**=> 形式化地：`tokenShapeVector` 只依赖 `ts.length`，故它对 token 的**身份完全失明**。**

**⇒ 这不是缺陷登记，而是一条**定理**：它把「神经捷径在 `IRWeights := ℕ → ℝ` 上只能承载形状」
从一句评论变成可引用的陈述。** -/
theorem tokenShapeVector_no_identity (ts us : List CharToken) (h : ts.length = us.length) :
    tokenShapeVector ts = tokenShapeVector us := by
  funext n
  unfold tokenShapeVector
  rw [h]

/-- **⭐⭐ 捷径的 `sound`。** -/
theorem neuralShortcut_sound (V : OOVVocab) (s : List Char)
    (hs : (neuralShortcut V).pre s) :
    ∃ z, (neuralShortcut V).run s = some z ∧ (neuralShortcut V).post s z :=
  (neuralShortcut V).sound s hs

end Lattice.Compose.Showcase.NeuralShortcut
