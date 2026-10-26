/-
# `EqConstraint` 的 tokenizer：`l1l2` 不再是恒等

## 0. 本节补什么

第 108 轮交付 `geoLadder` 时，`l1l2` 是单元素列表的占位实现：

```lean
l1l2 := { encode := fun c => [c], decode := fun ts => ts.head?, roundtrip := fun _ => rfl }
```

**根因不是懒惰，而是类型约束**：`Ladder Data Tok Sym W` 的 `Tok` 被 `l0l1` 与 `l1l2`
**共享**。当 `Tok = EqConstraint n` 时，`l1l2 : Tokenizer (EqConstraint n) (EqConstraint n)`
的任何实例都只能是「换个包装再拿回来」——**往返义务本身把内容压成了恒等**。

第 144–149 轮逐层把 `EqConstraint` 编码到 `EqTok := ℕ ⊕ ℝ`：

| 轮次 | 成果 |
|:--|:--|
| 144 | `SExpr ⇄ List ℕ` |
| 147 | `GeoExpr → List EqTok` |
| 148 | `decExpr_enc_nil`：`GeoExpr` 五构造子往返 |
| 149 | `decCon_enc_nil`：`EqConstraint` 四构造子往返 |

**本节把 `Tok` 改成 `EqTok`，于是 `l1l2` 有了实质内容。**

## 1. 主定义

```lean
def eqConstraintTokenizer : Tokenizer (EqConstraint n) EqTok where
  encode := encCon
  decode := fun ts => (decCon ts.length ts).map Prod.fst
  roundtrip := fun c => ...     -- 由 decCon_enc_nil
```

**`roundtrip` 不是假设，是从第 149 轮的定理读出来的**：`decCon_enc_nil c` 说
`decCon (encLenC c) (encCon c) = some (c, encLenC c)`，而 `encCon_length` 说
`(encCon c).length = encLenC c`，两者相除即得。

## 2. 非平凡性

```lean
theorem eqConstraintTokenizer_nontrivial :
    encode (.samePoint 3 4) = [Sum.inl cSamePoint, Sum.inl 3, Sum.inl 4]
```

**这一条是本节的全部意义**：占位实现的 `encode` 是 `[c]`（长度 1，内容是数据本身），
**本节的 `encode` 产出 3 个真正的 token，且每个都是编码过的 `ℕ ⊕ ℝ`。**

## 3. 边界（必须明说）

- **`Tok` 改变导致 `Data` 也改变**。`Ladder` 的 `Tok` 被两跳共享，所以把 `Tok` 从
  `EqConstraint n` 改成 `EqTok` 之后，`l0l1` 也必须是 `Tokenizer Data EqTok`。
  本节取 **`Data = EqConstraint n`**：**一个数据项就是一个约束**。
  于是 `l0l1` 与 `l1l2` 是同一个映射。
- **多约束数据集尚未支持**：那需要 `Tokenizer (List (EqConstraint n)) EqTok`，
  其解码需要 fuel 单调性（每个约束自定界，但列表解码的 fuel 记账需要额外引理）。
  **这是独立的一步，不在本节范围内。**
- **`L0` 与 `L2` 在本实例里同型**，所以这条 `Ladder` 的「数据层」与「符号层」在类型上重合。
  **这是本实例的范围限制，不是 `Ladder` 结构的缺陷**——别的实例可以用不同的 `Data`。
- 本节**不改** `satSym`/`satW`/`l2l3`/`l2l3_sound`，因此端到端定理的内容不变。
-/
import Mathlib
import Lattice.Geo.EqConstraintToken
import Lattice.Lift.EndToEnd

open Lattice.Geo
open Lattice.Geo.EqTok
open Lattice.Geo.EqTokRoundtrip
open Lattice.Geo.EqConstraintToken

namespace Lattice.Geo

namespace EqConstraintTokens

variable {n : ℕ}

/-- **约束的 tokenizer**：`encCon` 出去，`decCon` 回来。

`decCon` 的 fuel 取 token 列表长度，足够因为 `encLenC c = (encCon c).length`。 -/
def eqConstraintTokenizer : Lattice.Lift.Tokenizer (EqConstraint n) EqTok where
  encode := encCon
  decode := fun ts => (decCon ts.length ts).map Prod.fst
  roundtrip := fun c => by
    show (decCon (encCon (n := n) c).length (encCon (n := n) c)).map Prod.fst = some c
    rw [encCon_length (n := n) c]
    rw [decCon_enc_nil c]
    rfl

/-- **它不是恒等 tokenizer**：token 类型与数据类型不同，且编码真的产出多个 token。

**这一条是本模块存在的理由**——占位实现的 `encode` 是 `[c]`（长度 1，内容就是数据本身）。 -/
theorem eqConstraintTokenizer_nontrivial :
    (eqConstraintTokenizer (n := n)).encode (.samePoint 3 4) =
      [Sum.inl cSamePoint, Sum.inl 3, Sum.inl 4] := rfl

/-- **一个具体的往返实例**，说明 tokenizer 真的能计算。 -/
theorem eqConstraintTokenizer_roundtrip (a b : ℕ) :
    (eqConstraintTokenizer (n := n)).decode
      ((eqConstraintTokenizer (n := n)).encode (.samePoint a b)) =
      some (.samePoint a b) :=
  (eqConstraintTokenizer (n := n)).roundtrip (.samePoint a b)

/-- **`expr` 构造子也往返**：带一个非平凡表达式。 -/
theorem eqConstraintTokenizer_roundtrip_expr (p : ℕ) (axis : Fin n) :
    (eqConstraintTokenizer (n := n)).decode
      ((eqConstraintTokenizer (n := n)).encode
        (.expr (.add (.coord p axis) (.const 1)))) =
      some (.expr (.add (.coord p axis) (.const 1))) :=
  (eqConstraintTokenizer (n := n)).roundtrip _

end EqConstraintTokens

end Lattice.Geo
