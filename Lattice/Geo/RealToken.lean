/-
# 可携带实数的 token 类型：`ℕ ⊕ ℝ`

## 0. 本节补什么

`Ladder.l1l2 : Tokenizer Sym Tok` 只有**一个** token 类型。`GeoExpr` 含 `const (c : ℝ)`，
而第 144 轮闭合的 D1 编码器把表达式编到 `List ℕ`——**实数进不去**。

第 146 轮把编码拆成两条流（结构 `List ℕ` + 常量 `List ℝ`），证明了无损往返。
**但那两条流在 `Tokenizer` 里必须合成一个 token 类型**，否则 `l1l2` 只能用占位实现。

本节定义 `EqTok := ℕ ⊕ ℝ`：

| 含义 | 表示 |
|:--|:--|
| 结构标签（构造子） | `Sum.inl` 一个小整数 |
| 坐标下标 | `Sum.inl` 一个自然数 |
| **实常量** | **`Sum.inr` 一个实数** |

**关键**：`inr` 分支让常量真正进入 token 流，于是「token 流单独」也可以是无损的。

## 1. 一个必须绕开的障碍

`ℕ ⊕ ℝ` **没有 `DecidableEq`**（`ℝ` 没有）。所以解码器不能写 `if t = someToken`——
它必须**先用模式匹配把 `Sum.inl`/`Sum.inr` 分开**，再只在 `ℕ` 上做比较。

`decExpr` 的定义形式因此是：

```
| fuel + 1, Sum.inl t :: d :: rest => if t = tCoord then ...
| _ + 1, Sum.inr _ :: _ => none
```

**`Sum.inr` 不可能作为表达式的第一个 token**，所以最后一行是死分支，但它让模式匹配完整。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `encExpr` | 编码：`GeoExpr → List EqTok` |
| `encExpr_length` | 长度 = `encLenE` |
| **`decExpr`** | **带 fuel 的解码器** |
| `decExpr_coord` | **坐标往返**（3 个 token） |
| **`decExpr_const`** | **常量往返，且值原样返回**（2 个 token） |

## 3. 边界（必须明说）

- **二元分支的往返未做**。`decExpr` 的 `tAdd`/`tSub`/`tMul` 三个分支**已实现**，
  但它们的往返证明需要重做 D1 的归纳（token 类型不同，`cases` 要处理 `Sum` 的额外一层）。
  **这是机械工作，不是新障碍**——第 144 轮的两条 ★ 行配方直接适用。
- **`geoLadder` 的 `l1l2` 仍未换成本节的编码器**：那需要把 `l1l2` 的往返定理补齐（即上一条）。
- 本节**不声称** `Ladder` 的四跳在这里闭合。
- 本节**只做 `GeoExpr`**，不含 `EqConstraint` 的四个构造子标签。

## 4. 第 146 轮与本节的衔接

```
第 146 轮:  GeoExpr  ⇄  (List ℕ) × (List ℝ)     两条流，逐条证明
本节:       GeoExpr  →  List (ℕ ⊕ ℝ)            合成一个 token 类型
```

**两条流是「证明上清晰」的形态，单 token 类型是「`Ladder` 要求」的形态。**
**前者已完整证明；后者编码器与解码器已就位，缺三个二元分支的往返。**
-/
import Mathlib
import Lattice.Geo.Expr

namespace Lattice.Geo

namespace EqTok

variable {n : ℕ}

/-! ## 一、token 类型 -/

/-- **一个 token**：`inl` 是结构标签或坐标，**`inr` 是实常量**。 -/
abbrev EqTok : Type := ℕ ⊕ ℝ

/-- 结构标签。 -/
def tCoord : ℕ := 0
def tConst : ℕ := 1
def tAdd : ℕ := 2
def tSub : ℕ := 3
def tMul : ℕ := 4

@[simp] theorem tCoord_eq : tCoord = 0 := rfl
@[simp] theorem tConst_eq : tConst = 1 := rfl
@[simp] theorem tAdd_eq : tAdd = 2 := rfl
@[simp] theorem tSub_eq : tSub = 3 := rfl

/-! ## 二、编码 -/

/-- **编码**：常量变成 `inr c`，值原样保留。 -/
def encExpr : GeoExpr n → List EqTok
  | .coord p axis => [.inl tCoord, .inl p, .inl axis.val]
  | .const c => [.inl tConst, .inr c]
  | .add a b => .inl tAdd :: (encExpr a ++ encExpr b)
  | .sub a b => .inl tSub :: (encExpr a ++ encExpr b)
  | .mul a b => .inl tMul :: (encExpr a ++ encExpr b)

/-- 编码长度的计算式。 -/
def encLenE : GeoExpr n → ℕ
  | .coord _ _ => 3
  | .const _ => 2
  | .add a b => 1 + encLenE a + encLenE b
  | .sub a b => 1 + encLenE a + encLenE b
  | .mul a b => 1 + encLenE a + encLenE b

/-- **编码长度 = `encLenE`**。 -/
theorem encExpr_length (e : GeoExpr n) : (encExpr e).length = encLenE e := by
  induction e with
  | coord p axis => rfl
  | const c => rfl
  | add a b iha ihb =>
      show (Sum.inl tAdd :: (encExpr a ++ encExpr b)).length = 1 + encLenE a + encLenE b
      simp only [List.length_cons, List.length_append, iha, ihb, encLenE]
      omega
  | sub a b iha ihb =>
      show (Sum.inl tSub :: (encExpr a ++ encExpr b)).length = 1 + encLenE a + encLenE b
      simp only [List.length_cons, List.length_append, iha, ihb, encLenE]
      omega
  | mul a b iha ihb =>
      show (Sum.inl tMul :: (encExpr a ++ encExpr b)).length = 1 + encLenE a + encLenE b
      simp only [List.length_cons, List.length_append, iha, ihb, encLenE]
      omega

/-- 每个编码至少两个 token（一个标签 + 至少一个操作数）。 -/
theorem encExpr_ge_two (e : GeoExpr n) : 2 ≤ (encExpr e).length := by
  rw [encExpr_length]
  induction e with
  | coord p axis => show 2 ≤ 3; omega
  | const c => show 2 ≤ 2; exact Nat.le_refl 2
  | add a b iha ihb => show 2 ≤ 1 + encLenE a + encLenE b; omega
  | sub a b iha ihb => show 2 ≤ 1 + encLenE a + encLenE b; omega
  | mul a b iha ihb => show 2 ≤ 1 + encLenE a + encLenE b; omega

/-- **每个编码以 `Sum.inl` 开头**：这是 `decExpr` 的第一个模式能匹配的原因。 -/
theorem encExpr_head_inl (e : GeoExpr n) :
    ∃ (t : ℕ) (tl : List EqTok), encExpr e = Sum.inl t :: tl := by
  cases e with
  | coord p axis => exact ⟨_, _, rfl⟩
  | const c => exact ⟨_, _, rfl⟩
  | add a b => exact ⟨_, _, rfl⟩
  | sub a b => exact ⟨_, _, rfl⟩
  | mul a b => exact ⟨_, _, rfl⟩

/-! ## 三、解码器

**注意 `Sum` 的模式匹配**：`ℝ` 没有 `DecidableEq`，所以不能整体比较 token；
先把 `Sum.inl`/`Sum.inr` 分开，再只在 `ℕ` 上比较。 -/

/-- **解码器**：带 fuel，返回表达式与消费的 token 数。 -/
def decExpr : ℕ → List EqTok → Option (GeoExpr n × ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | fuel + 1, Sum.inl t :: d :: rest =>
      if t = tCoord then
        (match d, rest with
         | Sum.inl p, Sum.inl axisVal :: _ =>
             if h : axisVal < n then some (.coord p ⟨axisVal, h⟩, 3) else none
         | _, _ => none)
      else if t = tConst then
        (match d with
         | Sum.inr c => some (.const c, 2)
         | _ => none)
      else if t = tAdd then
        (match decExpr fuel (d :: rest) with
         | some (x, c₁) =>
             match decExpr fuel ((d :: rest).drop c₁) with
             | some (y, c₂) => some (.add x y, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else if t = tSub then
        (match decExpr fuel (d :: rest) with
         | some (x, c₁) =>
             match decExpr fuel ((d :: rest).drop c₁) with
             | some (y, c₂) => some (.sub x y, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else if t = tMul then
        (match decExpr fuel (d :: rest) with
         | some (x, c₁) =>
             match decExpr fuel ((d :: rest).drop c₁) with
             | some (y, c₂) => some (.mul x y, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else none
  | _ + 1, Sum.inr _ :: _ => none

/-! ## 四、叶子往返 -/

/-- **坐标往返**：3 个 token，还原坐标。 -/
theorem decExpr_coord (p : ℕ) (axis : Fin n) (fuel : ℕ) :
    decExpr (n := n) (fuel + 1) (encExpr (n := n) (.coord p axis)) = some (.coord p axis, 3) := by
  show decExpr (n := n) (fuel + 1)
      (Sum.inl tCoord :: Sum.inl p :: Sum.inl axis.val :: []) = some (.coord p axis, 3)
  rw [decExpr]
  simp only [tCoord_eq]
  norm_num

/-- **常量往返**：2 个 token，**且实数值原样返回**。

这是 `ℕ` token 类型做不到的事，也是本节引入 `Sum.inr` 的理由。 -/
theorem decExpr_const (c : ℝ) (fuel : ℕ) :
    decExpr (n := n) (fuel + 2) (encExpr (n := n) (.const c)) = some (.const c, 2) := by
  show decExpr (n := n) (fuel + 2) (Sum.inl tConst :: Sum.inr c :: []) = some (.const c, 2)
  rw [show (fuel + 2) = (fuel + 1) + 1 from rfl]
  rw [decExpr]
  simp only [tConst_eq, tCoord_eq]
  norm_num

end EqTok

end Lattice.Geo
