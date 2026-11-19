import Mathlib
import Lattice.Core.IR.DecodeStrict
import Lattice.Core.IR.DecodeRelations

/-!
# **把严格化传播到每一层**（阶段 Q，O-2 方案 A 完成）

## 上一轮留下的形状

**`DecodeStrict` 把忠实性变成**构造**：`strictly f enc` 只保留码正确的解码结果。**
**=> 但只实例化了张量形状一层。审计要的是**整个 `ℕ → Option IRSkeleton`**。**

## 本轮的抽象：只有一条前提需要验证

**`strictly` 的忠实性是**无条件的**（`strictly_faithful`，零前提）。**
**=> 唯一需要逐层提供的是「码能解回原值」，即各层**已有的** `_code` 定理。**

**=> 于是六层可以共用**一条**定理：**

```lean
theorem strictly_of_code (hcode : ∀ a, f (enc a) = some a) (a : α) :
    strictly f enc (enc a) = some a
```

**=> 六层的 `_Strict_code` 全部是它的一行实例。**

**=> 并且合并成一条**闭包性质**：**

```lean
theorem strictly_total_and_faithful (hcode : ∀ a, f (enc a) = some a) :
    (∀ n a, strictly f enc n = some a → enc a = n) ∧
    (∀ a, strictly f enc (enc a) = some a)
```

**=> 读法：**「宽松解码器只要在码上正确，它的严格化就**既不丢码、也不产假码**」。**

## 覆盖的六层

| 层 | 解码器 | 编码器 | 既有的 `_code` |
|:--|:--|:--|:--|
| **张量形状** | `decodeTensorShape` | `tensorShapeCode` | 上轮已实例化 |
| **张量列表** | `decodeTensorList` | `shapesCode tensorShapeCode` | `decodeTensorList_code` |
| **关系参数** | `decodeArgs` | `argsCode` | `decodeArgs_code` |
| **关系形状** | `decodeRelationShape` | `relationShapeCode` | `decodeRelationShape_code` |
| **关系列表** | `decodeRelList` | `shapesCode relationShapeCode` | `decodeRelList_code` |
| **骨架** | `decodeSkeleton` | `skeletonCode` | `decodeSkeleton_code` |

**=> `decodeList` 不在此列：它返回 `List ℕ` 而非 `Option`，故 `strictly` 不适用；
它的忠实性问题在第 973 轮由 `listCode`/`decodeList` 的非单射性单独处理。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`strictly_of_code`** | **⭐⭐⭐ 通用：码上正确 ⟹ 严格化在码上返回原值** |
| **`strictly_total_and_faithful`** | **⭐⭐⭐ 闭包性质：既不丢码、也不产假码** |
| **五层 × （`_code` + `_faithful`）** | **⭐⭐ 每层两条一行实例** | -/

namespace Lattice.Core.IR

/-! ## 一、通用抽象（六层共用） -/

/-- **⭐⭐⭐ 码上正确 ⟹ 严格化在码上返回原值。**

**=> 这是六层共用的**唯一前提**。各层只需提供自己的 `_code` 定理。** -/
theorem strictly_of_code {α : Type} (f : ℕ → Option α) (enc : α → ℕ)
    (hcode : ∀ a, f (enc a) = some a) (a : α) : strictly f enc (enc a) = some a :=
  strictly_code f enc (enc a) a (hcode a) rfl

/-- **⭐⭐⭐ 闭包性质：宽松解码器只要在码上正确，
其严格化**既不丢码、也不产假码**。** -/
theorem strictly_total_and_faithful {α : Type} (f : ℕ → Option α) (enc : α → ℕ)
    (hcode : ∀ a, f (enc a) = some a) :
    (∀ (n : ℕ) (a : α), strictly f enc n = some a → enc a = n) ∧
      (∀ a, strictly f enc (enc a) = some a) :=
  ⟨fun n a h => strictly_faithful f enc n a h, fun a => strictly_of_code f enc hcode a⟩

/-! ## 二、张量列表层 -/

/-- **⭐⭐ 张量列表的可计算忠实解码器。** -/
def decodeTensorListStrict (n : ℕ) : Option (List TensorShape) :=
  strictly decodeTensorList (shapesCode tensorShapeCode) n

/-- **⭐⭐ 不丢码。** -/
theorem decodeTensorListStrict_code (xs : List TensorShape) :
    decodeTensorListStrict (shapesCode tensorShapeCode xs) = some xs :=
  strictly_of_code decodeTensorList (shapesCode tensorShapeCode) decodeTensorList_code xs

/-- **⭐⭐ 不产假码。** -/
theorem decodeTensorListStrict_faithful {n : ℕ} {xs : List TensorShape}
    (h : decodeTensorListStrict n = some xs) : shapesCode tensorShapeCode xs = n :=
  strictly_faithful decodeTensorList (shapesCode tensorShapeCode) n xs h

/-! ## 三、关系参数层 -/

/-- **⭐⭐ 关系参数的可计算忠实解码器。** -/
def decodeArgsStrict (n : ℕ) : Option (List (TensorId × List ℕ)) :=
  strictly decodeArgs argsCode n

/-- **⭐⭐ 不丢码。** -/
theorem decodeArgsStrict_code (xs : List (TensorId × List ℕ)) :
    decodeArgsStrict (argsCode xs) = some xs :=
  strictly_of_code decodeArgs argsCode decodeArgs_code xs

/-- **⭐⭐ 不产假码。** -/
theorem decodeArgsStrict_faithful {n : ℕ} {xs : List (TensorId × List ℕ)}
    (h : decodeArgsStrict n = some xs) : argsCode xs = n :=
  strictly_faithful decodeArgs argsCode n xs h

/-! ## 四、关系形状层 -/

/-- **⭐⭐ 关系形状的可计算忠实解码器。** -/
def decodeRelationShapeStrict (n : ℕ) : Option RelationShape :=
  strictly decodeRelationShape relationShapeCode n

/-- **⭐⭐ 不丢码。** -/
theorem decodeRelationShapeStrict_code (r : RelationShape) :
    decodeRelationShapeStrict (relationShapeCode r) = some r :=
  strictly_of_code decodeRelationShape relationShapeCode decodeRelationShape_code r

/-- **⭐⭐ 不产假码。** -/
theorem decodeRelationShapeStrict_faithful {n : ℕ} {r : RelationShape}
    (h : decodeRelationShapeStrict n = some r) : relationShapeCode r = n :=
  strictly_faithful decodeRelationShape relationShapeCode n r h

/-! ## 五、关系列表层 -/

/-- **⭐⭐ 关系列表的可计算忠实解码器。** -/
def decodeRelListStrict (n : ℕ) : Option (List RelationShape) :=
  strictly decodeRelList (shapesCode relationShapeCode) n

/-- **⭐⭐ 不丢码。** -/
theorem decodeRelListStrict_code (rs : List RelationShape) :
    decodeRelListStrict (shapesCode relationShapeCode rs) = some rs :=
  strictly_of_code decodeRelList (shapesCode relationShapeCode) decodeRelList_code rs

/-- **⭐⭐ 不产假码。** -/
theorem decodeRelListStrict_faithful {n : ℕ} {rs : List RelationShape}
    (h : decodeRelListStrict n = some rs) : shapesCode relationShapeCode rs = n :=
  strictly_faithful decodeRelList (shapesCode relationShapeCode) n rs h

/-! ## 六、骨架层（审计 P1-8 的目标层） -/

/-- **⭐⭐⭐ 骨架层的可计算忠实解码器——这正是审计 P1-8 所要的函数，且**可计算**。**

**=> 与第 974 轮的 `decodeSpec`（`Classical.choose`，非可计算）**并列**：
两者都满足规格，`decodeSkeletonStrict` 额外**可计算**。** -/
def decodeSkeletonStrict (n : ℕ) : Option IRSkeleton :=
  strictly decodeSkeleton skeletonCode n

/-- **⭐⭐⭐ 不丢码：所有真实骨架码都被正确解回。** -/
theorem decodeSkeletonStrict_code (k : IRSkeleton) :
    decodeSkeletonStrict (skeletonCode k) = some k :=
  strictly_of_code decodeSkeleton skeletonCode decodeSkeleton_code k

/-- **⭐⭐⭐ 不产假码：非码一律得 `none`——审计 P1-8 的措辞，**由构造直接给出**。** -/
theorem decodeSkeletonStrict_faithful {n : ℕ} {k : IRSkeleton}
    (h : decodeSkeletonStrict n = some k) : skeletonCode k = n :=
  strictly_faithful decodeSkeleton skeletonCode n k h

/-- **⭐⭐⭐ 审计 P1-8 的**逐字形式**：非骨架码返回 `none`。**

**=> 由 `decodeSkeletonStrict_faithful` 的逆否直接得到。** -/
theorem decodeSkeletonStrict_none_of_not_code (n : ℕ)
    (h : ¬ ∃ k : IRSkeleton, skeletonCode k = n) : decodeSkeletonStrict n = none := by
  cases hn : decodeSkeletonStrict n with
  | none => rfl
  | some k =>
    exact absurd ⟨k, decodeSkeletonStrict_faithful hn⟩ h

end Lattice.Core.IR
