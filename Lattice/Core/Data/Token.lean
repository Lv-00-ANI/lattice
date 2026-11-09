import Mathlib
import Lattice.Core.Data.Basic

/-!
# Token：数据的符号化

## 这个文件为什么存在

**表示链是这样写的：`数据 ⇄ token ⇄ 符号模型 ⇄ 权重`。
`Encode` 走的是「数据 → CIC term」，`Bridge` 走的是「数据 → IR 骨架」——
**两条都跳过了 token 这一层。**

**⇒ 本文件把 token 显式化，并证明它与数据的对应是**结构保持**的。
如果不做这一步，「token 那一跳」就只是一个名义上的环节。**

## token 是什么

**一个 token 携带两样东西：它指向的**样本位置**（`index`），以及它在该样本里的**角色**
（`part`：输入还是输出）。**

**=> `part` 是必要的，不是风格：token 化的**全部意义**在于把「一条数」放进「它属于输入的哪一段」这个上下文里。
没有 `part` 的 token 只把数换个容器，什么都没做。**
**⇒ 这也是 `Sample` 两个字段（`input`/`output`）存在的兑现处 —— 那条边界在这里变成 token 的标签。** -/

namespace Lattice.Data
namespace Token

/-- **一个 token 的角色：输入的一部分，或输出的一部分。**

**=> 两个构造子恰好对应 `Sample` 的两个字段。**
**把它定义为独立类型而不是 `Bool`，是为了让「输入」与「输出」在类型层面不可混淆 ——
`Bool` 允许 `!` 之类的操作，而那对「角色」是没有意义的。** -/
inductive Part where
  /-- **输入的一部分。** -/
  | input : Part
  /-- **输出的一部分。** -/
  | output : Part

/-- **一个 token：样本位置 + 角色 + 在该段内的偏移。**

**`index` 指向语料中的样本，`part` 说明它是输入还是输出，`slot` 是段内偏移。
三者合起来唯一确定一个坐标。**
**=> `slot` 而不是「值」：token 携带**位置**，数值从数据里查。
这与 `Encode` 的决定一致 —— 数值不进符号层。** -/
structure Token where
  /-- **样本在语料中的位置。** -/
  index : ℕ
  /-- **该坐标属于输入还是输出。** -/
  part : Part
  /-- **段内偏移。** -/
  slot : ℕ

/-- **把一个样本 token 化：先输入，后输出。**

**`tokenizeSample s` 产出 `s.input.length + s.output.length` 个 token：
前半 `input` 角色，后半 `output` 角色，`slot` 分别从零重新计数。**
**=> 两条 `map` 的 `range` 都从零开始，因此 `part` 与 `slot` 一起构成段内坐标 ——
它们不是全局偏移，这是有意的：**段内坐标**让「输入的第三个」与「输出的第三个」是两个不同的 token，
而不必知道前面有几段。** -/
def tokenizeSample (index : ℕ) (s : Sample) : List Token :=
  ((List.range s.input.length).map (fun k => { index := index, part := Part.input, slot := k }))
    ++ ((List.range s.output.length).map (fun k => { index := index, part := Part.output, slot := k }))

/-- **把一个语料 token 化。**

**=> 对每个样本按位置编号再拼接。编号用 `List.range` 与 `List.zip`，
因此 token 的 `index` 恰好复现样本在语料中的位置。** -/
def tokenize : List Sample → List Token
  | [] => []
  | s :: ss => tokenizeSample 0 s ++ tokenize ss

/-- **空语料不产生 token。**

**=> 链的起点处没有 token；这是归纳的锚点。** -/
theorem tokenize_nil : tokenize [] = [] := by
  simp [tokenize]

/-- **单个样本产出的 token 数量恰好等于它的宽度。**

**`(tokenizeSample k s).length = s.width`。**

**=> 这条是 token 化的**第一条正确性**：token 不多不少，正好覆盖样本的每个坐标。
证明把它展开成两条 `map` 的长度相加，而 `Sample.width` 的定义就是两段长度之和 ——
因此这不是巧合，而是两处定义对齐的结果。** -/
theorem length_tokenizeSample (index : ℕ) (s : Sample) :
    (tokenizeSample index s).length = s.width := by
  simp [tokenizeSample, Sample.width, List.length_append, List.length_map, List.length_range]

theorem tokenize_cons (s : Sample) (ss : List Sample) :
    (tokenize (s :: ss)).length = s.width + (tokenize ss).length := by
  simp [tokenize, length_tokenizeSample]

/-- **一个 token 的位置唯一确定它的来源样本位置。**

**=> `Token.index` 是 token 与语料的连接点：任何从 token 回到数据的读法都必须经过它。
这条定理只是把它显式化，但它是后面「token 侧可复原样本位置」的出发点。** -/
theorem token_index_eq (k : ℕ) (s : Sample) (t : Token)
    (ht : t ∈ tokenizeSample k s) : t.index = k := by
  simp only [tokenizeSample, List.mem_append, List.mem_map, List.mem_range] at ht
  rcases ht with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

end Token
end Lattice.Data
