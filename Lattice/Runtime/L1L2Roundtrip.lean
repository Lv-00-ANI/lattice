/-
# L1 ⇄ L2 的往返定理

## 0. 本节补上什么

`Lattice.Lift.L1L2` 给出 `encodeForm`（符号 → token）与 `decodePayload`（token → 符号），
但**没有任何命题把它们联系起来**。所以「token 能还原成符号」在库中只是注释里的一句话，
`Geo/Pipeline.token_to_weight` 只能把 `decodePayload` 写进前提，而那个前提不承重。

本节补上往返定理，这是四跳中 L1 → L2 这一跳的**承重载体**。

## 1. 证明思路

`encodeForm c` 的 token 流按定义是

```
(finRange n).map (fun i => sym (c.a i)) ++ [sym c.b, sep]
```

`Encoded.payload` 对它做 `filterMap`：`sym r ↦ some r`、`sep ↦ none`。于是 payload 是
`[c.a 0, …, c.a (n-1), c.b]`，而 `decodePayload` 正是「取前 `n` 项作系数、第 `n` 项作常数」。

| 步骤 | 引理 |
|:--|:--|
| `filterMap` 穿透 `map sym` 与 `++` | `filterMap_sym_append` |
| 复合形式（`map (fun i => sym (f i))`） | `filterMap_comp_append` |
| payload = 系数列表 ++ [常数项] | `encodeForm_payload` |
| 第 `i < n` 项是 `c.a i` | `payload_getElem?_coeff` |
| 第 `n` 项是 `c.b` | `payload_getElem?_const` |
| 故 `decodePayload n payload = some c` | `decodePayload_encodeForm` |

## 2. 两处必须避开的陷阱（实测得出）

本文件此前六次失败，原因都在「重写模式不匹配」，不在数学：

**(a) 不要在归纳中混用 `payload` 与其展开式。**
`simp only [Encoded.payload]` 把目标里的 `payload` 展成 `List.filterMap ...`，
而归纳假设仍以 `payload` 的**缩写形式**出现。`payload` 是 `def`，两者命题等价但**语法不同**，
`rw` 按语法匹配，于是失败。
⇒ 归纳**直接对 `List.filterMap` 陈述**，不让 `payload` 参与归纳。

**(b) `l.map (fun i => sym (f i))` 与 `l.map sym` 不是同一个模式。**
它们由 `List.map_map` 相等，但 `rw` 看不到；先 `rw [← List.map_map]` 也不稳定，
因为复合的方向取决于目标的具体形态。
⇒ **直接对复合形式归纳**（`filterMap_comp_append`），不试图在两种形式间改写。

## 3. 承重性：证明了什么、没证明什么

**证明了**：`decodePayload n (encodeForm c).payload = some c`。

**没证明**：任何 token 流都能解码。后者**为假**——payload 太短时 `decodePayload`
返回 `none`（`decodeConst` 的 `none` 分支）。这是**拒绝垃圾输入**，不是缺陷。
两条界限不同：本节证**往返**，不证**全定义性**。

## 4. 边界

- `Inhabited R` 在 `decodePayload` 的签名里，但对**往返定理不起作用**：
  `getD` 只在索引越界时用默认值，而 `encodeForm` 保证不越界。
- 只做**单形式**往返。多段（`splitOn`）需要论证段边界，未做。
- **不做单射性**：`decodePayload` 不单射（长 payload 的尾部被丢弃），
  与 L0 的 `tokenize_not_injective` 同源，属设计而非缺陷。
-/
import Mathlib
import Lattice.Runtime.L1L2
namespace Lattice.Lift

namespace L1L2Roundtrip

open Lattice.Lift

variable {R : Type} [DecidableEq R] [Inhabited R]

/-! ## 一、`filterMap` 穿透 `map sym` 与 `++`

这两条对 `List.filterMap` **直接**陈述，不经 `Encoded.payload` 这个 `def`
——理由见文件头 §2(a)。 -/

/-- **`filterMap` 穿透一串 `sym`。** -/
theorem filterMap_sym_append (l : List R) (tail : List (Token R)) :
    List.filterMap (fun t => match t with | .sym r => some r | .sep => none)
        (l.map Token.sym ++ tail)
      = l ++ List.filterMap (fun t => match t with | .sym r => some r | .sep => none) tail := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.cons_append, List.filterMap_cons]
    rw [ih]

/-- **复合形式**：`map (fun i => sym (f i))` 的 `filterMap` 是 `map f`。

直接对复合形式归纳，不试图把它改写成 `map sym`——理由见文件头 §2(b)。 -/
theorem filterMap_comp_append {ι : Type} (l : List ι) (f : ι → R) (tail : List (Token R)) :
    List.filterMap (fun t => match t with | .sym r => some r | .sep => none)
        (l.map (fun i => Token.sym (f i)) ++ tail)
      = l.map f
        ++ List.filterMap (fun t => match t with | .sym r => some r | .sep => none) tail := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.cons_append, List.filterMap_cons]
    rw [ih]

/-! ## 二、`encodeForm` 的 payload 形状 -/

/-- **`encodeForm c` 的 payload 是「系数列表 ++ [常数项]」。** -/
theorem encodeForm_payload (n : Nat) (c : Lattice.Core.LinearForm R n) :
    (encodeForm c).payload = (List.finRange n).map (fun i => c.a i) ++ [c.b] := by
  have hshape : (encodeForm c).toks
      = (List.finRange n).map (fun i => Token.sym (c.a i)) ++ [Token.sym c.b, Token.sep] := rfl
  show (Encoded.payload ⟨(encodeForm c).arity, (encodeForm c).toks⟩ : List R) = _
  rw [hshape]
  exact filterMap_comp_append (List.finRange n) (fun i => c.a i) [Token.sym c.b, Token.sep]

/-- 该 payload 的长度是 `n + 1`。 -/
theorem encodeForm_payload_length (n : Nat) (c : Lattice.Core.LinearForm R n) :
    (encodeForm c).payload.length = n + 1 := by
  rw [encodeForm_payload]
  simp [List.length_finRange]

/-! ## 三、payload 的分量（`getElem?` 形式，避免依赖证明项） -/

/-- `finRange n` 的第 `i` 项（`i < n`）是 `⟨i, _⟩`。 -/
theorem finRange_getElem? {n : ℕ} {i : ℕ} (h : i < n) :
    (List.finRange n)[i]? = some (⟨i, h⟩ : Fin n) := by
  rw [List.getElem?_eq_getElem (by simpa using h)]
  rw [List.getElem_finRange]
  simp

/-- 第 `i` 项（`i < n`）是 `c.a i`。 -/
theorem payload_getElem?_coeff (n : Nat) (c : Lattice.Core.LinearForm R n) (i : Fin n) :
    (encodeForm c).payload[i.val]? = some (c.a i) := by
  rw [encodeForm_payload]
  rw [List.getElem?_append_left (by simp [List.length_finRange])]
  rw [List.getElem?_map]
  rw [finRange_getElem? i.isLt]
  rfl

/-- 第 `n` 项是常数项 `c.b`。 -/
theorem payload_getElem?_const (n : Nat) (c : Lattice.Core.LinearForm R n) :
    (encodeForm c).payload[n]? = some c.b := by
  rw [encodeForm_payload]
  rw [List.getElem?_append_right (by simp [List.length_finRange])]
  simp

/-! ## 四、解码在编码上的行为 -/

/-- **`decodeConst` 在编码上返回 `some c.b`。** -/
theorem decodeConst_encodeForm (n : Nat) (c : Lattice.Core.LinearForm R n) :
    decodeConst n (encodeForm c).payload = some c.b :=
  payload_getElem?_const n c

/-- **`decodeCoeffs` 的每一项是 `c.a i`。** -/
theorem decodeCoeffs_encodeForm (n : Nat) (c : Lattice.Core.LinearForm R n) (i : Fin n) :
    (decodeCoeffs n (encodeForm c).payload).getD i.val (default : R) = c.a i := by
  unfold decodeCoeffs
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt i.isLt]
  rw [payload_getElem?_coeff]
  rfl

/-! ## 五、往返定理 -/

/-- **`encodeForm` 与 `decodePayload` 在单形式上互逆。**

`decodePayload n (encodeForm c).payload = some c`。

此前 `encodeForm` 与 `decodePayload` 是两个孤立的定义，
「token 能还原成符号」只有注释支持；这条定理使其成为命题。 -/
theorem decodePayload_encodeForm (n : Nat) (c : Lattice.Core.LinearForm R n) :
    decodePayload n (encodeForm c).payload = some c := by
  unfold decodePayload
  rw [decodeConst_encodeForm]
  simp only
  congr 1
  cases c with
  | mk a b =>
    simp only
    congr 1
    funext i
    exact decodeCoeffs_encodeForm n ⟨a, b⟩ i

end L1L2Roundtrip

end Lattice.Lift
