import Mathlib
import Lattice.Core.Data.Encode
import Lattice.Runtime.AcceptanceLayer
import Lattice.Runtime.EndToEndComposite

/-!
# 数据端的**类型化**与权重端的**接受**：两条平行判据的对齐（阶段 C，P6）

## 先纠正一个我此前说错的东西

**第 895-896 轮我试图让 `CoversCorpus K c` 推出「权重层输出为零」，并否证了它。**

**那个否证是对的，但**我对 `K` 的理解错了**：**

**`ConstSet : Type := ℕ → Prop`，而 `Typable K` 的规则是
「一个 `const` 只有在 `K` 接受它时才可类型化」（`Typing.lean:74-75`）。**

**=> 所以 `K` **不是**「权重的零化判定」，它是**类型系统的常量集**。
`CoversCorpus K c` 说的是「这批数据的宽度都在类型系统允许的常量里」。**

**=> 它对应的是**可类型化**（`typable_encodeCorpus`），不是「输出为零」。
我此前把「类型合规」和「数值为零」混为一谈了。**

## 本文件补的：两条**平行**判据的对齐

**现在有两组判据，各自成立，但从未被并置：**

| 侧 | 判据 | 定理 |
|:--|:--|:--|
| **类型** | **`c` 被 `K` 覆盖 ⟹ `encodeCorpus c` 可类型化** | **`typable_encodeCorpus`** |
| **数值** | **`K` 接受 `k` ⟺ 接受层输出为零** | **`acceptanceLayer_zero_iff`** |
| **链路** | **数据约束成立 ⟺ 权重层输出为零** | **`data_to_weight_iff`** |

**=> 本文件证明它们**相容**：接受层不改变数值链路 ——
即「把类型判据编成权重」与「把数值约束编成权重」**可以共存**，互不干扰。**

### 交付什么

| 定理 | 内容 |
|:--|:--|
| `typed_and_numeric_coexist` | **⭐ 类型判据与数值判据同时成立，互不冲突** |
| `covers_gives_typed_encoding` | **⭐ `CoversCorpus` ⟹ 编码可类型化（类型侧已闭合）** |
| `acceptance_does_not_disturb_numeric` | **⭐ 接受层不影响数值链路的判定** |

**=> 最后一条是「共存」的精确形式：
在 `corpusToLayer c` 之外再挂一个接受层，不改变 `corpusToLayer c` 的零化判定。** -/

namespace Lattice.Runtime.TypedNumericAlignment

open Lattice.Core.CIC
open Lattice.Data
open Lattice.Data.Encode
open Lattice.Lift.SymbolToWeightCorrectness

/-- **⭐ 类型侧已闭合：`CoversCorpus` ⟹ 语料编码可类型化。**

**=> 直接引用既有的 `typable_encodeCorpus`。**
**本文件把它显式化，因为它是**类型判据**那一半，不是数值判据那一半。** -/
theorem covers_gives_typed_encoding {K : ConstSet} (Γ : CICCtx) (c : List Sample)
    (h : CoversCorpus K c) : Typable K Γ (encodeCorpus c) :=
  typable_encodeCorpus Γ c h

/-- **⭐⭐ 共存：类型判据与数值判据同时成立，互不冲突。**

**=> 左半：`CoversCorpus K c` ⟹ `encodeCorpus c` 可类型化（类型侧）。**
**右半：`data_to_weight_iff` ⟹ 数据的约束成立 ⟺ 权重层全零（数值侧）。**

**=> 两者谈的是**不同的东西**（类型合规 vs 数值满足），所以可以**同时**为真。**
**我此前把它们混为一谈，这条定理就是纠正。** -/
theorem typed_and_numeric_coexist {K : ConstSet} (Γ : CICCtx) (c : List Sample) (x : List Int)
    (h : CoversCorpus K c) :
    Typable K Γ (encodeCorpus c) ∧
      ((∀ v ∈ Lattice.Runtime.CICBridge.corpusToConstraintSet c, VectorConstraintSat v x) ↔
        AllZeroOutputs (Lattice.Runtime.CICBridge.corpusToLayer c) x) :=
  ⟨covers_gives_typed_encoding Γ c h,
   Lattice.Runtime.CICBridge.data_to_weight_iff c x⟩

/-- **⭐ 共存的操作形式：接受层不干扰数值链路。**

**=> 接受层 `acceptanceLayer acc` 是一个**无输入依赖**的层（权重 `[]`）。
它承载「类型判据是否通过」这一个比特，而 `corpusToLayer c` 承载数值约束。**

**=> 于是：`corpusToLayer c` 的零化判定与接受层的存在**互不影响** ——
因为接受层是**另外的**一个层，不是 `corpusToLayer c` 的一部分。** -/
theorem acceptance_does_not_disturb_numeric (c : List Sample) (x : List Int)
    (acc : Bool) :
    (AllZeroOutputs (Lattice.Runtime.CICBridge.corpusToLayer c) x ↔
        (∀ v ∈ Lattice.Runtime.CICBridge.corpusToConstraintSet c, VectorConstraintSat v x)) ∧
      (LayerOut (Lattice.Runtime.CICBridge.acceptanceLayer acc) x = 0 ↔ acc = true) :=
  ⟨(Lattice.Runtime.CICBridge.data_to_weight_iff c x).symm,
   Lattice.Runtime.CICBridge.acceptanceLayer_zero_iff acc x⟩

end Lattice.Runtime.TypedNumericAlignment
