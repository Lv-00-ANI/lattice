import Mathlib
import Lattice.Core.CIC.Syntax
import Lattice.Core.IR.Semantics

/-!
# 数据核心：表示链的源头

## 这个文件为什么存在

**表示链是 `数据 ⇄ token ⇄ 符号模型 ⇄ 权重`。阶段 0 归档了几何层之后，链的上游 —— 「数据」——
在主线里**没有任何载体**：`Core/IR` 从 `Term` 开始，`Core/CIC` 从语法开始，而「数据」被默认成
「你喂给它的任何东西」。**

**⇒ 本文件把「数据」变成一个**具体的、可编码的**类型，因此链的起点不再是假设。**

## 设计取舍：为什么不是 `List ℝ`

**最省事的做法是 `Data := List ℝ`，但那会把三件事混为一谈：**
**1. 一个**样本**（输入 + 目标输出）；**
**2. 一个**语料**（样本的序列）；**
**3. 一个**索引结构**（哪些位置属于同一个样本）。**

**`List ℝ` 只表达第 1 层的一部分，并且丢掉「哪些是输入、哪些是目标」这条边界 ——
而那条边界正是「数据」与「一堆数」的区别，也是后面 `encode` 能保持类型的前提。**
**⇒ 所以 `Data` 是一个结构：`corpus`（样本序列）+ `indices`（索引）。**

## 与 CIC / IR 的关系

**本文件只定义数据本身，不涉及编码。**
**`Data.Encode` 把 `Data` 编成 CIC `Term`；`Data.Bridge` 把它编成 `IRSkeleton`；
`Data.Models` 证明两条路在语义上给出同一个验证结论。**
**⇒ 分文件的原因：加法顺序是 `Basic → Equiv → Encode → Decode → Bridge → Token → Models`，
而把它们塞进一个文件会让「哪条引理依赖哪个表示」变成隐式的。** -/

namespace Lattice.Data

/-- **一个样本：输入序列与目标输出序列。**

**两个字段分开是**实质决定**，不是风格：`List ℝ` 无法区分「这条数是输入」与「这条数是答案」，
而任何训练信号都需要那条边界。**
**⇒ 后面 `encode` 的保类型性正是靠这条边界：输入坐标与输出坐标落在 term 的不同位置。** -/
structure Sample where
  /-- **输入部分。** -/
  input : List ℝ
  /-- **目标输出部分。** -/
  output : List ℝ

/-- **一个索引：语料中的一段可寻址区间。**

**`offset` 是起点，`length` 是长度。**
**=> 用 `ℕ × ℕ` 而不是 `Fin` 索引，是因为数据在编码前不应当被假定落在范围内 ——
「索引越界」是**数据的问题**，不是类型的问题，而 `DataValid` 会把这件事说清楚。** -/
structure Index where
  /-- **起点。** -/
  offset : ℕ
  /-- **长度。** -/
  length : ℕ

/-- **数据：语料 + 索引结构。**

**=> 这是整条链的起点。它携带两样东西：样本序列本身，以及「哪些样本属于同一个逻辑单位」的分组。**
**第二个字段常常被省略，而不省略它是为了后面 `bridge` 能证明「索引结构在编码后仍然可恢复」。** -/
structure Data where
  /-- **样本序列。** -/
  corpus : List Sample
  /-- **索引结构。** -/
  indices : List Index

/-- **空数据**：没有样本，也没有索引。

**=> 链的起点必须有一个显式的空值，否则「编码空数据」这件事没有指称对象。**
**它也是 `DataValid` 的平凡实例（见下）。** -/
def Data.empty : Data :=
  { corpus := [], indices := [] }

/-- **一个样本对数据的**要求**：索引必须落在语料范围内。**

**`DataValid d` 说：每个索引的区间都在语料的长度之内。**
**=> 这不是「数据是好数据」的价值判断，而是一条**可判定的结构条件**，而 `Encode.encode_sound` 用它来保证
编码出的 term 有类型 —— 越界的索引会让编码出的 term 指向不存在的样本，那就不是有类型的项。**
**⇒ 把条件写成显式的谓词而不是编码时的 `Option`，是因为数据层的职责是**刻画**哪些数据可用，
而不是把不可用的悄悄丢掉。** -/
def DataValid (d : Data) : Prop :=
  ∀ i ∈ d.indices, i.offset + i.length ≤ d.corpus.length

/-- **空数据是有效的。**

**=> `DataValid` 的基例，也是后面所有 `*_nil` 引理的锚点。** -/
theorem dataValid_empty : DataValid Data.empty := by
  intro i hi
  simp [Data.empty] at hi

/-- **样本的宽度：输入长度 + 输出长度。**

**=> 编码需要知道一个样本占多少个坐标，`width` 是那个数。**
**定义成 `input.length + output.length` 而不是取最大值，是因为编码是**拼接**：先写输入，再写输出。** -/
def Sample.width (s : Sample) : ℕ :=
  s.input.length + s.output.length

/-- **语料的总宽度。**

**=> 把每个样本的 `width` 加起来。它是「这批数据一共涉及多少个数」的答案，
而 `Bridge` 用它来分配张量编号。** -/
def Corpus.width (c : List Sample) : ℕ :=
  (c.map Sample.width).sum

/-- **空语料的总宽度为零。**

**=> 归纳基例：链的起点处没有任何数。** -/
theorem corpus_width_nil : Corpus.width [] = 0 := by
  simp [Corpus.width]

/-- **总宽度在拼接下相加。**

**`width (c₁ ++ c₂) = width c₁ + width c₂`。**
**=> 这条使「两个数据集的编码可以拼接」成为严格等式，而不只是单向不等式。
它是 `Bridge` 里分块构造张量的基础。** -/
theorem corpus_width_append (c₁ c₂ : List Sample) :
    Corpus.width (c₁ ++ c₂) = Corpus.width c₁ + Corpus.width c₂ := by
  simp [Corpus.width, List.map_append, List.sum_append]

end Lattice.Data
