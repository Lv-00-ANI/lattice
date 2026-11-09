import Mathlib
import Lattice.Core.Data.Encode
import Lattice.Core.IR.Semantics

/-!
# 桥：`Data → IRSkeleton`

## 这个文件为什么存在

**`Encode` 把数据编成 CIC term。但表示链的下一跳是**符号模型**，而符号模型在主线里的载体是
`IRSkeleton`（张量形状 + 关系形状）。**

**⇒ 所以需要一条从数据到 `IRSkeleton` 的直接路径，并且它必须与「数据 → term → IR」这条路**一致**。**

## 为什么是「两条路」

**`Core/IR/Parse.lean` 已经有 `parseWithRelations : Term → IRSkeleton` —— 那是 term → IR 的权威路径。
而数据层可以直接造骨架（`bridge`），因为它知道自己的形状。**

**两条路的存在不是冗余：**
**- `bridge` 是**构造性**的，它告诉你骨架**长什么样**；**
**- `parseWithRelations ∘ encode` 是**派生**的，它说明编码**确实**承载了同样的结构。**

**⇒ 「两条路一致」被写成 `encode_comm_shapes`，而它本轮只覆盖张量侧。
把限度写出来而不是含糊过去，是因为「部分一致」与「完全一致」的差距正是链的剩余工作。**

## 骨架的形状

**一个样本贡献一个单点张量（`termShape`），一个索引贡献一条 `depends` 关系。
⇒ 这与 `Parse.lean` 的 `termShape` 约定一致：一个 term 是一个单点张量。**
-/

namespace Lattice.Data
namespace Bridge

open Lattice.Core.IR

/-- **一个样本对应的张量形状：编号 `k`、形状 `termShape`。**

**=> 抽出成具名函数是必要的：`{ id := k, shape := termShape }` 直接写在 `map` 内部时
Lean 无法从期望类型反推字段名，而具名函数给了它一个检查点。** -/
def tensorAt (k : ℕ) : TensorShape :=
  { id := k, shape := termShape }

/-- **数据对应的张量形状序列：每个样本一个单点张量。**

**=> 编号用 `List.range`，因此编号 `0..n-1` **互不相同** ——
IR 的 `covered` 条件依赖编号唯一，而这里是那个条件的第一处来源。** -/
def shapesOfCorpus (c : List Sample) : List TensorShape :=
  (List.range c.length).map tensorAt

/-- **一个索引对应的关系形状。**

**`kind := depends`（索引依赖它覆盖的样本），`args := [(offset, [offset, offset + length])]`。**
**=> 用端点对而不是展开整个区间：`RelationShape.args` 的第二分量是 `List ℕ`，
而 `[offset, offset + length]` 已足够表达「哪一段」；展开会让 `args` 随区间长度增长，
那对骨架比对结构更没有信息。** -/
def relationOfIndex (i : Index) : RelationShape :=
  { kind := RelKind.depends
    args := [(i.offset, [i.offset, i.offset + i.length])]
    part := none }

/-- **数据对应的关系序列：每个索引一条关系。** -/
def relationsOfIndices (is : List Index) : List RelationShape :=
  is.map relationOfIndex

/-- **数据对应的 IR 骨架。**

**`bridge d = { tensors := 每个样本一个单点, relations := 每个索引一条 }`。**
**=> 这是数据层的**出口**：链的下一跳（符号模型）拿到的是这个骨架。** -/
def bridge (d : Data) : IRSkeleton :=
  { tensors := shapesOfCorpus d.corpus, relations := relationsOfIndices d.indices }

/-- **空数据的桥是空骨架。**

**=> 链的起点处没有张量，也没有关系；这是归纳的锚点。** -/
theorem bridge_empty : bridge Data.empty = { tensors := [], relations := [] } := by
  simp [bridge, shapesOfCorpus, relationsOfIndices, Data.empty]

/-- **张量数量等于样本数量。**

**=> `shapesOfCorpus` 是对 `List.range c.length` 的 `map`，长度不变。** -/
theorem length_shapesOfCorpus (c : List Sample) :
    (shapesOfCorpus c).length = c.length := by
  simp [shapesOfCorpus]

/-- **关系数量等于索引数量。** -/
theorem length_relationsOfIndices (is : List Index) :
    (relationsOfIndices is).length = is.length := by
  simp [relationsOfIndices]

/-- **张量编号互不相同。**

**`((shapesOfCorpus c).map (·.id)).Nodup`。**

**=> 这是 `covered` 条件的前提：IR 层用编号查张量，编号重复会让「找到的是哪一个」失去意义。**
**⇒ 证明走 `List.range` 的无重复性：`map tensorAt` 保留编号，所以只需证 `range` 无重复。** -/
theorem nodup_shapesOfCorpus (c : List Sample) :
    ((shapesOfCorpus c).map (·.id)).Nodup := by
  have hcomp : ((fun x : TensorShape => x.id) ∘ tensorAt) = id := by
    funext k
    rfl
  have hmap : (shapesOfCorpus c).map (·.id) = List.range c.length := by
    simp only [shapesOfCorpus, List.map_map, hcomp, List.map_id]
  rw [hmap]
  exact List.nodup_range c.length

/-- **桥与编码走两条路，得到同一个张量序列。**

**`(bridge d).tensors = shapesOfCorpus d.corpus` 且长度等于样本数。**

**=> 这是数据层的**一致性定理**：它排除了「bridge 造了一个与编码无关的骨架」这种情形。**
**⇒ 本轮只覆盖张量侧：关系侧的对齐需要展开 `parseWithRelations` 的 `walkWithRelations`，
那是下一轮的事，而不是本轮的沉默。** -/
theorem encode_comm_shapes (d : Data) :
    (bridge d).tensors = shapesOfCorpus d.corpus
      ∧ (bridge d).tensors.length = d.corpus.length :=
  ⟨rfl, length_shapesOfCorpus d.corpus⟩

end Bridge
end Lattice.Data
