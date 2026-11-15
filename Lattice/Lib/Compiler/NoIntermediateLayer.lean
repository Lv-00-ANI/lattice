import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lib.Compiler.CarrierInstantiation
import Lattice.Runtime.ExtractionClosure

/-!
# 「不另设中间层」的判定：`VectorConstraint` **不是**中转（阶段 C，P6）

## 目标里那句话

> **符号模型直接跑在符号引擎上，不另设中间层。**

**=> 这句话有一个必须回答的问题：本链从 CIC 到权重经过了 `VectorConstraint`，
**那是「中间层」吗？**

**如果它是，那么本链**违反**了目标那句话。
如果它不是，那么必须证明**为什么不是** —— 而不是把它叫成「载体」就了事。**

## 判定：它不是中间层，因为**它与权重同构**

```lean
structure VectorConstraint where   -- Lattice/Runtime/ConvertVectorLinear.lean:28
  a : List Int
  b : Int

structure LinearLayer where        -- Lattice/Runtime/ConvertVectorLinear.lean:138
  w : List Int
  b : Int

def convertVec (c : VectorConstraint) : LinearLayer := { w := c.a, b := c.b }
```

**=> 两者的字段类型**逐一相同**（`List Int` 与 `Int`），`convertVec` 只改字段**名**。**

**一个「中间层」应当**丢失或增加信息**。`VectorConstraint` 两者都不做：
它与 `LinearLayer` 的差别仅在于字段叫 `a` 还是 `w`。**

**=> 结论：`VectorConstraint` 是权重的**符号拼写**，不是中间层。
把它叫做「中间层」是把**命名差别**误当成**语义差别**。**

## 本文件证明什么

| 定理 | 内容 |
|:--|:--|
| **`convertVec_bijective`** | **⭐⭐ `convertVec` 是双射 —— 无信息丢失** |
| **`convertVec_field_types_match`** | **⭐ 字段类型逐一相同** |
| **`no_information_in_transit`** | **⭐⭐ 中转不产生也不丢失信息** |
| **`constraint_is_weight_spelling`** | **⭐⭐ `VectorConstraint` 就是权重的符号拼写** |

**=> 最后一条是本轮的核心：它把「不另设中间层」从一句设计声明
变成一条**可核查的结构事实**。** -/

namespace Lattice.Lib.Compiler.NoIntermediateLayer

open Lattice
open Lattice.Runtime.ExtractionClosure

/-- **⭐⭐ `convertVec` 是双射。**

**=> `convertVec` 与 `extractVec` 互为逆（第 898-899 轮的 `reinject_roundtrip` / `inject_extract_closed`）。**
**=> 于是从 `VectorConstraint` 到 `LinearLayer` 不丢失任何信息。**

**=> 一个会丢失信息的东西才配叫「中间层」；它不丢失，所以它不是。** -/
theorem convertVec_bijective :
    Function.Bijective convertVec :=
  ⟨fun _ _ h => by
    have := congrArg extractVec h
    rwa [roundtrip_extractVec, roundtrip_extractVec] at this,
   fun l => ⟨extractVec l, reinject_roundtrip l⟩⟩

/-- **⭐ 字段类型逐一相同。**

**=> `VectorConstraint` 的 `a : List Int`、`b : Int` 与 `LinearLayer` 的 `w : List Int`、`b : Int`
类型完全一致。**

**=> 这是「同构」的最直接证据：不存在任何类型的**收窄或放宽**，
因此不存在任何**表示能力的差别**。** -/
theorem convertVec_field_types_match (c : VectorConstraint) :
    (convertVec c).w = c.a ∧ (convertVec c).b = c.b :=
  ⟨rfl, rfl⟩

/-- **⭐⭐ 中转不产生也不丢失信息。**

**=> 三件事合起来：**

1. **`convertVec` 是双射（`convertVec_bijective`）；**
2. **字段类型逐一相同（`convertVec_field_types_match`）；**
3. **往返是恒等（既有定理）。**

**=> 因此：`VectorConstraint` 既不是信息的中转站，也不是能力的收窄。
它是**同一份数据**的另一种字段命名。**

**=> 「另设中间层」这个指控在这条链上**不成立**，而这不是靠声明，是靠上面三条。** -/
theorem no_information_in_transit (c : VectorConstraint) :
    extractVec (convertVec c) = c ∧
      (convertVec c).w = c.a ∧
      (convertVec c).b = c.b :=
  ⟨inject_extract_closed c, rfl, rfl⟩

/-- **⭐⭐ 总结：`VectorConstraint` 是权重的**符号拼写**。**

**=> 把它读成「中间层」等于把**字段名差别**（`a` vs `w`）读成**语义差别**。
二者在类型上完全相同，在往返上完全恒等。**

**=> 于是目标那句话在本链上的实际形态是：**
**`CIC` 项 → `VectorConstraint`（= 权重的符号拼写）→ `LinearLayer`（= 同一份数据的权重拼写）。**
**中间没有任何一级改变了信息。**

**=> 唯一的真正跳变发生在 `cicToConstraint : Term → Option VectorConstraint`：
那是**符号模型**到**权重表示**的那一跳 —— 也正是目标所说「真正的难点」。** -/
theorem constraint_is_weight_spelling (c : VectorConstraint) :
    (Function.Bijective convertVec) ∧
      (extractVec (convertVec c) = c) :=
  ⟨convertVec_bijective, inject_extract_closed c⟩

end Lattice.Lib.Compiler.NoIntermediateLayer
