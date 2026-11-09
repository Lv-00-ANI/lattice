import Mathlib
import Lattice.Core.Data.Bridge
import Lattice.Core.Data.Decode
import Lattice.Core.Data.Token

/-!
# 端到端：数据 ⇄ 权重

## 这个文件为什么存在

**`Basic`/`Equiv`/`Encode`/`Decode`/`Bridge`/`Token` 各自给出链的一段。
本文件把它们接起来，回答整条链的**唯一需要端到端回答的问题**：**

**> 给定一份数据，是否存在一组权重，它被 `models` 判定为「实现了这份数据」？**

**`data_models` 就是那条定理，而且它是**零前提**的（在 `Covered` 之外）。**

## 这一跳为什么不需要额外内容

**`Core/IR/Extract.lean` 已经证了 `models_compileWith`：对任意骨架与任意权重读取，`compileWith` 造出的权重
被 `models` 接受。**
**⇒ 数据层不需要重新证明权重侧 —— 它只需要**把数据变成一个骨架**（`bridge`），
然后让 IR 层已证的事实在那个骨架上生效。**

**这正是分层的意义：**符号⇄权重那一跳的难度已经在 `Core/IR` 里付清，
数据层付的是另一份账 —— 把数据变成骨架。**

## 本文件证明了什么，以及刻意没证明什么

**证明了：**
**- `data_models`：`bridge d` 与它编译出的权重满足 `models`（端到端闭环）；**
**- `data_models_shape`：该权重的读取在形状层面与数据的样本数一致；**
**- `token_count`：token 总数等于语料的宽度（token 侧的守恒）；**
**- `decode_shape_roundtrip`：数据 → term → 数据保持形状。**

**刻意没证明：**
**- `bridge d` 与 `parseWithRelations (encode d)` 的**关系侧**相等（见 `Bridge.encode_comm_shapes` 的说明）；**
**- 数值的可复原性（`Encode` 的决定：数值不进符号层）。**

**⇒ 把「没证明的」写在这里，是因为它们是链的剩余工作，而把它们留成沉默会让下一个人重新发现一遍。**
-/

namespace Lattice.Data
namespace Models

open Lattice.Core.IR

/-- **端到端：数据编出的骨架与它编译出的权重满足 `models`。**

**`models (bridge d) (compileWith (bridge d) f) f`，对**任意**读取函数 `f`。**

**=> 这是目标所说「数据 ⇄ 权重」那一跳的闭环：数据经 `bridge` 变成骨架，
骨架经 `compileWith` 变成权重，而 `models` 判定该权重实现了该骨架。**
**⇒ 定理零前提 —— 除了 `f` 可以任意之外没有别的假设。
`f` 任意是关键：它说明**任何**读取约定都能被这条链接受，链不捆绑某种具体的权重布局。**
**证明直接引用 IR 层已有的 `models_compileWith`：数据层的职责是造骨架，权重侧的难度已在 IR 层付清。** -/
theorem data_models (d : Data)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    models (Bridge.bridge d) (compileWith (Bridge.bridge d) f) f :=
  models_compileWith (Bridge.bridge d) f (Bridge.nodup_shapesOfCorpus d.corpus)

/-- **该权重的骨架张量数等于样本数。**

**=> 把 `models` 的结论与数据的形状接起来：权重的坐标数不是任意的，
它等于 `bridge d` 的张量数，而后者等于语料长度。**
**⇒ 这条使「数据的规模」与「权重的规模」之间有一条可读的等式，
而不只是「存在某个权重」。** -/
theorem data_models_shape (d : Data)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    (Bridge.bridge d).tensors.length = d.corpus.length :=
  Bridge.length_shapesOfCorpus d.corpus

/-- **token 侧守恒：token 总数等于语料的宽度。**

**`(Token.tokenize d.corpus).length = Corpus.width d.corpus`。**

**=> 这条把 `Token` 与 `Basic` 的数字接起来：token 数不多不少，正好覆盖每个样本的每个坐标。
证明对语料归纳，用 `length_tokenizeSample`（单样本守恒）与 `corpus_width_append`（宽度可加）。** -/
theorem token_count (c : List Sample) :
    (Token.tokenize c).length = Corpus.width c := by
  induction c with
  | nil => simp [Token.tokenize, Corpus.width]
  | cons s ss ih =>
      have hstep : (Token.tokenize (s :: ss)).length
          = (Token.tokenizeSample 0 s).length + (Token.tokenize ss).length := by
        simp [Token.tokenize, List.zip_cons_cons, List.flatMap_cons]
      rw [hstep, Token.length_tokenizeSample, ih]
      simp [Corpus.width, List.map_cons, List.sum_cons]

/-- **数据经 term 往返后形状不变。**

**=> `Decode.decode_encode_shape` 的端到端读法：数据 → term → 数据保持样本数与顺序。
这条与 `data_models` 并列，说明链的两个方向各自保住了什么：
**正向保住语义（`models`），反向保住形状（样本数）。** -/
theorem decode_shape_roundtrip (d : Data) :
    ∃ d' : Data, Decode.decode (Encode.encode d) = some d'
      ∧ d'.corpus.length = d.corpus.length := by
  obtain ⟨d', hdec, hlen, _⟩ := Decode.decode_encode_shape d
  exact ⟨d', hdec, hlen⟩

end Models
end Lattice.Data
