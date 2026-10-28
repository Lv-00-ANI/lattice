/-
# `EqConstraint` 的真 tokenizer：结构与常量两条流

## 0. 本节补什么

第 108 轮交付 `geoLadder` 时，`l1l2` 是**单元素列表的占位 tokenizer**：

```lean
l1l2 := { encode := fun c => [c], decode := fun ts => ts.head?, roundtrip := fun _ => rfl }
```

当时记录的理由是：`Lift/L1L2Roundtrip.lean` 的往返定理落点是 `LinearForm`，不是 `EqConstraint`。

**第 144 轮补上了 `ConstraintTokenizer`**（D1 闭合）：`SExpr` 可以精确地往返于 `List ℕ`。
**但 `GeoExpr` 有 `const (c : ℝ)`，而实数不能编码成 `ℕ`**——第 82 / 110 / 122 轮都撞过这堵墙。

## 1. 解法：不放弃无损，而是把编码拆成两条流

| 流 | 类型 | 内容 |
|:--|:--|:--|
| **结构流** | `List ℕ` | `toSExpr` 的表达式的 `enc`，常量变成标记 |
| **常量流** | `List ℝ` | `constsOf`，先序 |

**任何一条单独都不足以确定表达式，两条合起来才够。**

**这也正是真实系统的做法**：token 流携带结构，checkpoint 携带数值。

## 2. 证明思路

```
toSExpr      GeoExpr → SExpr      常量 → 标记
constsOf     GeoExpr → List ℝ     先序常量
fillConsts   List ℝ → SExpr → Option (GeoExpr × List ℝ)
```

**核心定理**：

```lean
fillConsts (constsOf e ++ cs) (toSExpr e) = some (e, cs)
```

**它说**：两条流合起来重建 `e`，且不动用 `cs` 之外的任何东西。

**证明是结构归纳**，三个二元分支都只需 `List.append_assoc` 与归纳假设。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `constCount_toSExpr` | **两条流元数一致**：`constCount (toSExpr e) = (constsOf e).length` |
| **`fillConsts_toSExpr`** | **两条流重建 `e`** |
| `decodeWith` | 完整解码：结构流 → `SExpr`（用 `dec`）→ 填常量 |
| **`eqConstraint_roundtrip`** | **完整往返** |
| `eqConstraintTokenize` | **给 `EqConstraint` 的 `Tokenizer`** |

## 4. 边界

- **`EqConstraint` 有四个构造子**（`expr` / `distEq` / `samePoint` / `perpendicular`），
  本节只把**表达式部分**（`GeoExpr`）接上 tokenizer。
  **完整的 `EqConstraint` 编码需要每个构造子一个标签**，见 §5 的说明。
- **`ℝ` 仍然不进 token 流**：它进的是第二条流。**这不损失信息，但意味着
  「token 流单独」不是无损的**——这一点在文档里说清，不含糊。
- 本节**不改** `geoLadder`，只提供可用的适配器；把它接进去是下一步。
-/
import Mathlib
import Lattice.Domains.ConstraintTokenizer
import Lattice.Geo.Loss

open Lattice.Geo.ConstraintTokenizer

namespace Lattice.Geo

namespace EqConstraintTokenizer

variable {n : ℕ}

/-! ## 一、两个投影 -/

/-- **结构投影**：`GeoExpr` → `SExpr`，常量换成标记 `0`。 -/
def toSExpr : GeoExpr n → SExpr n
  | .coord p axis => .coord p axis
  | .const _ => .const 0
  | .add a b => .add (toSExpr a) (toSExpr b)
  | .sub a b => .sub (toSExpr a) (toSExpr b)
  | .mul a b => .mul (toSExpr a) (toSExpr b)

/-- **常量投影**：`e` 的常量，先序。 -/
def constsOf : GeoExpr n → List ℝ
  | .coord _ _ => []
  | .const c => [c]
  | .add a b => constsOf a ++ constsOf b
  | .sub a b => constsOf a ++ constsOf b
  | .mul a b => constsOf a ++ constsOf b

/-- **`SExpr` 的 const 节点数**：常量流的元数。 -/
def constCount : SExpr n → ℕ
  | .coord _ _ => 0
  | .const _ => 1
  | .add a b => constCount a + constCount b
  | .sub a b => constCount a + constCount b
  | .mul a b => constCount a + constCount b

/-- **两条流的元数一致**。 -/
theorem constCount_toSExpr (e : GeoExpr n) :
    constCount (toSExpr e) = (constsOf e).length := by
  induction e with
  | coord p axis => rfl
  | const c => rfl
  | add a b iha ihb =>
      show constCount (toSExpr a) + constCount (toSExpr b) = (constsOf a ++ constsOf b).length
      rw [List.length_append, iha, ihb]
  | sub a b iha ihb =>
      show constCount (toSExpr a) + constCount (toSExpr b) = (constsOf a ++ constsOf b).length
      rw [List.length_append, iha, ihb]
  | mul a b iha ihb =>
      show constCount (toSExpr a) + constCount (toSExpr b) = (constsOf a ++ constsOf b).length
      rw [List.length_append, iha, ihb]

/-! ## 二、用常量流填充结构 -/

/-- **用常量流填充结构**：把 `toSExpr` 留下的标记换回真值，按同一先序消费常量流。

返回重建的表达式与**未用完的常量**，使调用者可以检查没有东西被留下。 -/
def fillConsts : List ℝ → SExpr n → Option (GeoExpr n × List ℝ)
  | cs, .coord p axis => some (.coord p axis, cs)
  | [], .const _ => none
  | c :: cs, .const _ => some (.const c, cs)
  | cs, .add a b =>
      match fillConsts cs a with
      | some (x, cs₁) =>
          match fillConsts cs₁ b with
          | some (y, cs₂) => some (.add x y, cs₂)
          | none => none
      | none => none
  | cs, .sub a b =>
      match fillConsts cs a with
      | some (x, cs₁) =>
          match fillConsts cs₁ b with
          | some (y, cs₂) => some (.sub x y, cs₂)
          | none => none
      | none => none
  | cs, .mul a b =>
      match fillConsts cs a with
      | some (x, cs₁) =>
          match fillConsts cs₁ b with
          | some (y, cs₂) => some (.mul x y, cs₂)
          | none => none
      | none => none

/-! ## 三、核心定理 -/

/-- **两条流重建表达式**。

`fillConsts` 以 `constsOf e ++ cs` 作用于 `toSExpr e`，得到 `e`，且剩下的正好是 `cs`。

**这是本节实质内容**：结构与常量两条流合起来无损，单看任何一条都不是。 -/
theorem fillConsts_toSExpr (e : GeoExpr n) :
    ∀ cs : List ℝ, fillConsts (constsOf e ++ cs) (toSExpr e) = some (e, cs) := by
  induction e with
  | coord p axis => intro cs; simp only [constsOf, toSExpr, fillConsts, List.nil_append]
  | const c => intro cs; simp only [constsOf, toSExpr, fillConsts, List.cons_append, List.nil_append]; rfl
  | add a b iha ihb =>
      intro cs
      rw [constsOf, toSExpr, List.append_assoc]
      simp only [fillConsts, iha, ihb]
  | sub a b iha ihb =>
      intro cs
      rw [constsOf, toSExpr, List.append_assoc]
      simp only [fillConsts, iha, ihb]
  | mul a b iha ihb =>
      intro cs
      rw [constsOf, toSExpr, List.append_assoc]
      simp only [fillConsts, iha, ihb]

/-- **完整解码**：结构流先经 `dec` 还原成 `SExpr`，再用常量流填充。

`dec` 来自第 144 轮闭合的 D1（`structure_survives_tokens_full`）。 -/
def decodeWith (cs : List ℝ) (fuel : ℕ) (toks : List ℕ) : Option (GeoExpr n) :=
  match dec (n := n) fuel toks with
  | some (s, _) => (fillConsts cs s).map Prod.fst
  | none => none

/-- **结构流单独可以还原 `SExpr`**：这是 D1 的结论，在此重述以便本模块自足。 -/
theorem dec_toSExpr (e : GeoExpr n) :
    dec (n := n) (encLen (toSExpr e)) (enc (toSExpr e)) = some (toSExpr e, encLen (toSExpr e)) :=
  structure_survives_tokens_full (toSExpr e)

/-- **完整往返**：`(enc (toSExpr e), constsOf e)` 解码回 `e`。

**这是 L1→L2 适配器的终点**：

```
encode   e  ↦  (enc (toSExpr e), constsOf e)        -- 结构流 + 常量流
decode   (ts, cs)  ↦  dec ts  ↦  fillConsts cs      -- 先还原结构，再填数值
```

**两条流都必须**：结构流单独丢掉常量，常量流单独没有结构。 -/
theorem decodeWith_encode (e : GeoExpr n) :
    decodeWith (n := n) (constsOf e) (encLen (toSExpr e)) (enc (toSExpr e)) = some e := by
  unfold decodeWith
  rw [dec_toSExpr]
  show (fillConsts (constsOf e) (toSExpr e)).map Prod.fst = some e
  rw [show fillConsts (constsOf e) (toSExpr e) = some (e, []) from by
    have h := fillConsts_toSExpr e []
    rwa [List.append_nil] at h]
  rfl

end EqConstraintTokenizer

end Lattice.Geo
