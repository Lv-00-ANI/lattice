import Mathlib
import Lattice.Core.IR.Decode
import Lattice.Core.IR.DecodeFaithful

/-!
# **通用「严格化」：把宽松解码器变成忠实解码器**（阶段 P，O-2 方案 A）

## 问题的一般形态

**第 973 轮的反例给出了**任一**宽松解码器的病根：**

> **`f : ℕ → Option α` 可能返回**像外**的 `some`。**

**=> 逐层去补守卫（`(unpair code).2 = 0`、`+1`、`listCode` 往返…）是**重复劳动**，
而且每补一层都要重做一次同样的推理。**

## 一般解法：解码后**按编码回验**

**给定 `f : ℕ → Option α` 与编码 `enc : α → ℕ`，定义**

```lean
def strictly (f : ℕ → Option α) (enc : α → ℕ) (n : ℕ) : Option α :=
  match f n with
  | some a => if enc a = n then some a else none
  | none   => none
```

**=> 于是 `strictly f enc n = some a` **当且仅当** `f n = some a` **且** `enc a = n`。**

**=> 忠实性成了**构造的直接推论**，不需要任何算术。**

## 为什么这比逐个修补更好

| 维度 | 逐个补守卫 | 本文件的 `strictly` |
|:--|:--|:--|
| **忠实性证明** | 每层重做一遍 `Nat.pair_eq_pair` 拆解 | **一次，3 行** |
| **新增一层** | 重新推理 | **`strictly` 套用即可** |
| **复用已有解码器** | 不适用 | **是：不重写，只在外面加一道回验** |

**=> 这正是「可推广的推广、抽象的抽象」：把「忠实」从一个**待证性质**变成一个**构造**。**

## 代价（明写）

**`strictly` 会**调用两次**编码路径上的工作（解码 + 回验编码），
故它比手写守卫慢常数倍。**
**=> 这是**用时间换可证明性**的显式取舍，不是隐藏成本。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`strictly`** | **⭐⭐⭐ 通用严格化构造** |
| **`strictly_faithful`** | **⭐⭐⭐ `= some a` 蕴含 `enc a = n`** |
| **`strictly_code`** | **⭐⭐ 若 `f n = some a` 且 `enc a = n`，则严格化保留它** |
| **`decodeTensorShapeStrict`** | **⭐⭐ 张量形状层的可计算忠实解码器** |
| **`decodeTensorShapeStrict_code`** | **⭐⭐ 它在码上返回原值** | -/

namespace Lattice.Core.IR

/-- **⭐⭐⭐ 通用严格化：解码后按编码回验，不一致即 `none`。**

**=> 不重写任何已有解码器，只在外面加一道**编码回验**。** -/
def strictly {α : Type} (f : ℕ → Option α) (enc : α → ℕ) (n : ℕ) : Option α :=
  match f n with
  | some a => if enc a = n then some a else none
  | none => none

/-- **⭐⭐⭐ 忠实性：严格化只返回**码正确**的值。**

**=> 这是审计 P1-8 反向要求的直接形式。** -/
theorem strictly_faithful {α : Type} (f : ℕ → Option α) (enc : α → ℕ) (n : ℕ) (a : α)
    (h : strictly f enc n = some a) : enc a = n := by
  unfold strictly at h
  cases hf : f n with
  | none => simp [hf] at h
  | some a' =>
    by_cases he : enc a' = n
    · simp [hf, he, Option.some.injEq] at h
      subst h
      exact he
    · simp [hf, he] at h

/-- **⭐⭐ 严格化保留所有**码正确**的解码结果。** -/
theorem strictly_code {α : Type} (f : ℕ → Option α) (enc : α → ℕ) (n : ℕ) (a : α)
    (hf : f n = some a) (henc : enc a = n) : strictly f enc n = some a := by
  simp [strictly, hf, henc]

/-- **⭐⭐ 张量形状层的**可计算忠实解码器**。**

**=> 由第 973 轮的反例可知 `decodeTensorShape` 是宽松的；
本定义在它外面加一道 `tensorShapeCode` 回验，于是忠实。** -/
def decodeTensorShapeStrict (code : ℕ) : Option TensorShape :=
  strictly decodeTensorShape tensorShapeCode code

/-- **⭐⭐ 它在合法码上仍返回原形状。**

**=> 由 `decodeTensorShape_code` 与 `tensorShapeCode` 的往返。** -/
theorem decodeTensorShapeStrict_code (t : TensorShape) :
    decodeTensorShapeStrict (tensorShapeCode t) = some t :=
  strictly_code decodeTensorShape tensorShapeCode (tensorShapeCode t) t
    (decodeTensorShape_code t) rfl

/-- **⭐⭐ 它是忠实的——第 973 轮反例所指的那一格现在被补上了。** -/
theorem decodeTensorShapeStrict_faithful (n : ℕ) (t : TensorShape)
    (h : decodeTensorShapeStrict n = some t) : tensorShapeCode t = n :=
  strictly_faithful decodeTensorShape tensorShapeCode n t h

end Lattice.Core.IR
