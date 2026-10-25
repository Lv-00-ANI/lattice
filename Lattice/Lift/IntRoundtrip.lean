/-
# 整数往返：`Int ⇄ List Char`（一元编码）

## 0. 本节补什么

第 66 轮关闭了 L1 字母表的**字符层**，并显式登记了数值层：

```lean
def IntRoundtripExists : Prop :=
  ∃ (enc : Int → List Char) (dec : List Char → Option Int), ∀ z, dec (enc z) = some z
```

**本节证明它。**

## 1. 证明思路：为什么用一元编码

先试十进制（`Nat.digits 10 n` + `Char.ofNat`）。它需要三样本版本 Mathlib 里**没有**的东西：
`Char.toNat_ofNat`、`Nat.length_digits_pos`、以及一组 `Nat.digits` 与 `List.map` 的交互引理。

**这些与「整数能否往返」无关，只增加证明量。**

**改用一元编码**：`n` 写成 `n` 个 `'1'`。

| 方向 | 定义 |
|:--|:--|
| 编码 | `List.replicate n '1'` |
| 解码 | `count '1'` |
| 往返 | `(replicate n '1').count '1' = n`，**一行 `List.count_replicate_self`** |

**一元编码不实用（长度 = 数值），但它证明的性质与十进制完全相同**：
存在单射编码且被解码还原。**这是「字母表可否连通」的正确抽象层次。**

## 2. 设计要点：`charsToInt` 用 `if` 而非 `match`

`match cs with '-' :: rest => ...` 在 `unfold` 后留下未归约的 `match`，
`rw` 看不到里面的 `count (replicate ...)` 模式。**用 `if` 判断首元素**，
展开后得到普通 `ite`，`simp`/`rw` 能直接化简。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `natToChars` / `charsToNat` | `Nat ⇄ List Char`（一元） |
| `charsToNat_natToChars` | **`Nat` 往返** |
| `intToChars` / `charsToInt` | `Int ⇄ List Char` |
| **`int_roundtrip`** | **`charsToInt (intToChars z) = some z`** |
| **`IntRoundtripExists_holds`** | **关闭第 66 轮登记的命题** |

## 4. 边界

- **一元编码不实用**：长度 = 数值。换成十进制时**往返定理的形状不变**，只是证明变长。
- `0` 编码为空列表；`Int` 的 `-0 = 0`，**无损失**。
- 解码器对非规范输入返回某个值而非 `none`（只数 `'1'`）。
  **这不破坏往返**（往返从 `enc` 出发），但 `dec` 不是单射。**已记录。**
-/
import Mathlib
import Lattice.Lift.TokenAlphabet

namespace Lattice.Lift

namespace IntRoundtrip

open Lattice.Lift.TokenAlphabet

/-! ## 一、`Nat ⇄ List Char`（一元编码） -/

/-- **自然数 → 字符列表**：`n` 个 `'1'`。 -/
def natToChars (n : ℕ) : List Char := List.replicate n '1'

/-- **字符列表 → 自然数**：数 `'1'` 的个数。 -/
def charsToNat (cs : List Char) : Option ℕ := some (cs.count '1')

/-- **`Nat` 往返**。 -/
theorem charsToNat_natToChars (n : ℕ) : charsToNat (natToChars n) = some n := by
  unfold charsToNat natToChars
  rw [List.count_replicate_self]

/-! ## 二、`Int ⇄ List Char` -/

/-- **整数 → 字符列表**：`tag :: 一元载荷`，**没有 `if`**。

`tag` 是 `'p'`（非负）或 `'n'`（负），载荷是数值的一元表示。
**两边都不做 `if` 分派**，因此解码可以按列表的**语法形状**直接匹配。 -/
def intToChars (z : Int) : List Char :=
  if 0 ≤ z then 'p' :: List.replicate z.toNat '1'
  else 'n' :: List.replicate ((-z).toNat - 1) '1'

/-- **字符列表 → 整数**：按首字符分派（`match`，不是 `head?`）。 -/
def charsToInt : List Char → Option Int
  | 'p' :: rest => some (((rest.count '1' : ℕ) : Int))
  | 'n' :: rest => some (-(((rest.count '1' : ℕ) : Int) + 1))
  | _ => none

/-- **整数往返（非负）**：`'p'` 分支。 -/
theorem int_roundtrip_nonneg {z : Int} (hz : 0 ≤ z) :
    charsToInt (intToChars z) = some z := by
  have h : intToChars z = 'p' :: List.replicate z.toNat '1' := by
    unfold intToChars
    rw [if_pos hz]
  rw [h]
  simp only [charsToInt, List.count_replicate_self]
  congr 2
  omega

/-- **整数往返（负）**：`'n'` 分支。

数值为 `negSucc n`，即 `-(n+1)`，所以载荷长度为 `n = (-z).toNat - 1`。 -/
theorem int_roundtrip_neg {z : Int} (hz : z < 0) :
    charsToInt (intToChars z) = some z := by
  have hpos : 0 < (-z).toNat := by omega
  have h : intToChars z = 'n' :: List.replicate ((-z).toNat - 1) '1' := by
    unfold intToChars
    rw [if_neg (by omega)]
  rw [h]
  simp only [charsToInt, List.count_replicate_self]
  have hz' : z = -(((-z).toNat : Int)) := by omega
  rw [hz']
  congr 2
  omega

/-- **整数往返**。 -/
theorem int_roundtrip (z : Int) : charsToInt (intToChars z) = some z := by
  rcases le_or_lt 0 z with h | h
  · exact int_roundtrip_nonneg h
  · exact int_roundtrip_neg h

/-! ## 三、关闭第 66 轮登记的命题 -/

/-- **`IntRoundtripExists` 成立**——第 66 轮登记为待做，本节完成。 -/
theorem IntRoundtripExists_holds : Lattice.Lift.TokenAlphabet.IntRoundtripExists :=
  ⟨intToChars, charsToInt, int_roundtrip⟩

end IntRoundtrip

end Lattice.Lift
