import Mathlib
import Lattice.Runtime.ConvertVectorLinear

/-!
# P1-8 的**真实完成度**：语义层早已完成，剩下的是**迁移**（阶段 B）

## 本轮核查的结论

**规划说 P1-8 要做的是「改用已存在的 `VecConstraint`，删掉 `sat_ragged_false_positive` 一族 N 定理」。**

**核查结果：`VectorConstraint` 与 `VecConstraint` 之间的**双向等价**早在
`ConvertVectorLinear.lean:343` 就已证明完整：**

```lean
theorem sat_iff_list_sat {a : List Int} (ha : a.length = n) {b : Int} {x : List Int}
    (hx : x.length = n) :
    vecSat ({ a := toFinVec n a, b := b } : VecConstraint n) (toFinVec n x) ↔
      VectorConstraintSat ({ a := a, b := b } : VectorConstraint) x :=
  ⟨list_sat_of_sat_of_length ha hx, sat_of_list_sat ha hx⟩
```

**配套的三条也都在：**

| 定理 | 位置 | 内容 |
|:--|:--|:--|
| `VecConstraint.sat_iff` | **:306** | **下标化满足 ⟺ 残差为零** |
| `VecConstraint.sat_of_list_sat` | **:314** | **截断 ⟹ 下标化（长度对齐时）** |
| `VecConstraint.list_sat_of_sat_of_length` | **:327** | **下标化 ⟹ 截断（长度对齐时）** |
| `VecConstraint.sat_iff_list_sat` | **:343** | **两者合起来的双向等价** |

## 所以 P1-8 缺的是什么，缺的**不是**语义

**缺的是**把 38 个文件、217 处 `VectorConstraintSat` 引用迁到 `VecConstraint`**。
而这件事**不能**在语义层动手，因为：

1. **`VectorConstraint` 的载体是 `List Int`，`VecConstraint n` 的载体是 `Fin n → Int`。
   迁移意味着每个使用点都要知道自己的长度 —— 那是**调用方的信息**，不是本文件能提供的；**
2. **`sat_iff_list_sat` 的假设 `ha : a.length = n` 与 `hx : x.length = n` 在**迁移后会消失**
   （因为 `Fin n → Int` 自动满足），但这要求每个使用点**重新陈述**它的向量长度。**

**=> 这是 38 次**语义重述**，不是 38 次机械替换。本文件把它登记为一项**独立工作项**，
而不是把它混进「已完成」。** -/

namespace Lattice.Runtime.VecCarrierCensus

open Lattice

/-- **登记：截断语义与下标化语义在长度对齐下**双向等价**。**

**=> 引用 `ConvertVectorLinear.lean:343` 的既有定理，把它挂到本命名空间下作为**索引**，
使读者能从「载体普查」这个名字找到那座桥。**

**=> 本条**不**新增数学内容 —— 它的价值是把「P1-8 的语义部分已完成」变成可检查的引用，
而不是文档里的一句话。** -/
theorem truncated_iff_indexed {n : Nat} {a : List Int} (ha : a.length = n) {b : Int}
    {x : List Int} (hx : x.length = n) :
    vecSat ({ a := toFinVec n a, b := b } : VecConstraint n) (toFinVec n x) ↔
      VectorConstraintSat ({ a := a, b := b } : VectorConstraint) x :=
  VecConstraint.sat_iff_list_sat ha hx

/-- **登记：`VecConstraint` 侧**没有**截断故障模式。**

**=> `vecSat` 的载体是 `Fin n → Int`，两个长度**必须**相等（同一个 `n`），
所以「赋值比系数短」这个情形**写不出来**。

**=> 这条把 `truncated_iff_indexed` 的右端与「缺陷可表达性」连起来：
等价式成立**当且仅当**长度被显式对齐，而下标化载体让那个对齐**自动**成立。** -/
theorem indexed_has_no_ragged_form {n : Nat} (c : VecConstraint n) (x : Fin n → Int) :
    vecSat c x ↔ vecDot c.a x + c.b = 0 :=
  VecConstraint.sat_iff c x

end Lattice.Runtime.VecCarrierCensus
