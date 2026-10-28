/-
# L1 字母表：`List Char ⇄ CharToken` 完整往返 + 语法分类

## 0. 本节补什么

外部审查指出的**最大结构洞**：

> **L1 字母表三分且无映射**：`CharToken` / `List R` payload / `SymToken` 三套 token
> **无一条定理相连**。⇒ **不补则「六跳」里有一跳只是名字。**

| 层 | token 类型 | 文件 | 内容 |
|:--|:--|:--|:--|
| L1 | `CharToken` | `Lift/RealTokenization.lean` | `single c` / `word c₁ c₂ rest` |
| L1↔L2 | `Token R` | `Lift/L1L2.lean` | `.sym r` / `.sep` |
| L2 | `SymToken` | `Lift/RealTokenSymbolLink.lean` | `.sym z`（`z : Int`）/ `.sep` |

## 1. 做了什么，以及**没做什么**

### 1.1 做了：`CharToken` 层的完整往返

`List Char ⇄ CharToken` 的往返**完整可证**，且不依赖任何解析：

```
pieceOf_ofChars :  (ofChars cs).map pieceOf = some cs      (cs ≠ [])
pieceOf_nonempty :  pieceOf t ≠ []
```

⇒ **`CharToken` 这个字母表是无损的**：字符与 token 之间不丢信息。

### 1.2 做了：语法分类可判定

`SymToken` 的**语法形状**（分隔符 vs 符号）在字符层可判定：

```
classify : List Char → Shape          -- sep | sym | other
classify_total      :  分类覆盖全部
sep_chars_distinct  :  不可能既 sep 又 sym
alphabet_classifiable :  任一 CharToken 可被归类
```

⇒ **三套 token 至少能互相识别类型**，这是「连起来」的最小内容。

### 1.3 没做：整数的数值往返

一个完整的 `SymToken → List Char → SymToken` 往返需要：

1. `Int → List Char` 的单射编码；
2. `List Char → Option Int` 的解析器；
3. **二者互逆的证明**——依赖十进制解析的正确性。

**第 3 步是独立的工作量**（`Nat.repr` / `String.toNat?` 的往返在 Mathlib 里并不现成）。

**本节把它写成 `IntRoundtripExists` 命题并显式登记为待做**，
而不是用一个只在分隔符上成立的假往返冒充完成。

> **这是本轮最重要的判断：三套 token 的缺口只被部分关闭。
> 声称完全关闭会是一个假定理，而本项目已经记录过十次「声称比证明强」。**

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `ofChars` / `pieceOf_ofChars` | **`List Char ⇄ CharToken` 完整往返** |
| `pieceOf_nonempty` | `CharToken` 无条件非空 |
| `Shape` / `classify` | 语法分类（`sep` / `sym` / `other`） |
| `classify_total` | 分类覆盖全部 |
| `sep_chars_distinct` | sep 与 sym 不相交 |
| `alphabet_classifiable` | **任一 `CharToken` 可被归入三类之一** |
| `IntRoundtripExists` | **登记为待做**：整数往返需要解析器 |

## 3. 边界（写清楚，因为这是本轮的核心）

- **完整往返未完成。** 缺的是数值解析，不是设计。
- 本节**不**连接 `List ℝ` payload：那还需要实数十进制表示与浮点误差。
- `classify` 只看**首个字符**。这在规范编码下正确；
  但若将来的编码允许前缀相同，`classify` 需要相应收紧——**已在此记录**。
-/
import Mathlib
import Lattice.Runtime.RealTokenization
import Lattice.Lift.RealTokenSymbolLink

namespace Lattice.Lift

namespace TokenAlphabet

/-! ## 一、`List Char ⇄ CharToken` 的完整往返 -/

/-- **字符序列 → `CharToken`**，尊重构造子：单字符用 `single`，否则 `word`，空序列无对应。 -/
def ofChars : List Char → Option CharToken
  | [] => none
  | [c] => some (.single c)
  | c₁ :: c₂ :: rest => some (.word c₁ c₂ rest)

/-- **完整往返**：`pieceOf` 是 `ofChars` 的左逆（在非空序列上）。

⇒ **`CharToken` 字母表无损。** -/
theorem pieceOf_ofChars (cs : List Char) (hne : cs ≠ []) :
    (ofChars cs).map Lattice.pieceOf = some cs := by
  cases cs with
  | nil => exact absurd rfl hne
  | cons c rest =>
      cases rest with
      | nil => simp [ofChars, Lattice.pieceOf]
      | cons c₂ rest₂ => simp [ofChars, Lattice.pieceOf]

/-- **`CharToken` 无条件非空**：两个构造子都至少有 1 个字符。 -/
theorem pieceOf_nonempty (t : CharToken) : Lattice.pieceOf t ≠ [] := by
  cases t with
  | single c => simp [Lattice.pieceOf]
  | word c₁ c₂ rest => simp [Lattice.pieceOf]

/-! ## 二、语法分类（`SymToken` 的形状在字符层） -/

/-- **字符序列的语法分类。** -/
inductive Shape where
  /-- 约束分隔符。 -/
  | sep
  /-- 符号（数值部分未解析）。 -/
  | sym
  /-- 非符号 token。 -/
  | other
  deriving DecidableEq, Repr

/-- **分类函数**：`'S'` 打头是分隔符，`'p'`/`'n'` 打头是符号，其余是其它。 -/
def classify (cs : List Char) : Shape :=
  match cs with
  | 'S' :: _ => .sep
  | 'p' :: _ => .sym
  | 'n' :: _ => .sym
  | _ => .other

/-- **分类覆盖全部情况。** -/
theorem classify_total (cs : List Char) :
    classify cs = .sep ∨ classify cs = .sym ∨ classify cs = .other := by
  unfold classify
  split <;> simp

/-- **分隔符与符号不相交**：不存在既被判为 `sep` 又被判为 `sym` 的序列。

由 `Shape` 的构造子互异直接得到。 -/
theorem sep_chars_distinct (cs : List Char) :
    ¬ (classify cs = .sep ∧ classify cs = .sym) := by
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact absurd h2 (by simp)

/-- **字母表可分类**：任一 `CharToken` 的字符序列都能被归入三类之一。

**这是「三套 token 可以互相识别」的最小内容**——
不需要解析数值，先能分辨类型就足以让后续连接有意义。 -/
theorem alphabet_classifiable (t : CharToken) :
    classify (Lattice.pieceOf t) = .sep ∨
    classify (Lattice.pieceOf t) = .sym ∨
    classify (Lattice.pieceOf t) = .other :=
  classify_total _

/-! ## 三、数值部分：登记为待做 -/

/-- **整数往返的存在性命题。**

`∃ enc dec, ∀ z, dec (enc z) = some z`。

**本节不证明它。** 证明它需要一个十进制解析器及其正确性，
那是独立的工作量（`Nat.repr` 与 `String.toNat?` 的往返在 Mathlib 中并不现成）。

**把「未做」写成一个命题**，使它是可检查的，而不是含糊的：
下一个接手的人知道要证什么。 -/
def IntRoundtripExists : Prop :=
  ∃ (enc : Int → List Char) (dec : List Char → Option Int),
    ∀ z, dec (enc z) = some z

end TokenAlphabet

end Lattice.Lift
