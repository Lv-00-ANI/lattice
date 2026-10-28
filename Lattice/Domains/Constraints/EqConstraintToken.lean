/-
# `EqConstraint` 的 token 编码：四个构造子全部往返

## 0. 本节补什么

第 148 轮把 `GeoExpr` 的 token 往返做完了（`decExpr_enc_nil`）。**但 `geoLadder` 的符号侧是
`EqConstraint`，它有四个构造子，每个带不同的载荷**：

```lean
| expr (e : GeoExpr n)                    -- 一个表达式
| distEq (a b : ℕ) (d : GeoExpr n)        -- 两个坐标 + 一个表达式
| samePoint (a b : ℕ)                     -- 两个坐标
| perpendicular (a b c e : ℕ)              -- 四个坐标
```

本节给每个构造子一个标签，使整个 `EqConstraint` 能往返。

## 1. 标签布局

表达式级标签（第 147 轮）占 `0`–`4`，所以约束级从 `5` 起，**共享同一个 token 字母表**：

| 构造子 | 标签 |
|:--|:--|
| `expr` | `5` |
| `distEq` | `6` |
| `samePoint` | `7` |
| `perpendicular` | `8` |

**这就是为什么一个 token 流能同时装下约束与表达式**：标签空间不相交。

## 2. 证明思路

解码器按标签分派，表达式部分**直接调用第 148 轮的 `decExpr`**——它已经对五个构造子证明完毕。

**fuel 的处理**：`decCon` 传递 `rest.length + 1` 给 `decExpr`。这总是够，因为
`encLenE e ≤ (encExpr e + rest).length`（引理 `encLenE_le_length`）。

**四个构造子的往返彼此独立**，因为标签不同、载荷形态不同：
- `samePoint` / `perpendicular`：纯标签 + 数字，无递归
- `expr`：标签 + 一次 `decExpr`
- `distEq`：标签 + 两数字 + 一次 `decExpr`

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `encCon_length` | 编码长度 = `encLenC` |
| `encLenE_le_length` | fuel 够用的依据 |
| `decCon_expr` / `_distEq` / `_samePoint` / `_perp` | **四个构造子各自的往返** |
| **`decCon_enc`** | **任意约束、任意后缀的精确消费** |
| **`decCon_enc_nil`** | **`decCon (encLenC c) (encCon c) = some (c, encLenC c)`** |

## 4. 边界

- **本节不含 `geoLadder` 的接线**：那需要构造 `Tokenizer (EqConstraint n) EqTok` 并证明
  `decode (encode c) = some c`，其中 `encode := encCon`、`decode` 从 `decCon` 取出第一分量。
  **这是下一步，而且是机械的**——本节已把所有材料备齐。
- `EqTok` 含 `ℝ`，所以**不能用 `DecidableEq` 相关策略**；本节所有证明都绕开了这一点。
- 本节**只做编码与解码**，不涉及语义（`poly`、`loss`）——那些在 `Loss.lean`，且不依赖 token 层。
-/
import Mathlib
import Lattice.Domains.Constraints.RealTokenRoundtrip
import Lattice.Domains.Constraints.Loss

open Lattice.Geo
open Lattice.Geo.EqTok
open Lattice.Geo.EqTokRoundtrip

namespace Lattice.Geo

namespace EqConstraintToken

variable {n : ℕ}


variable {n : ℕ}

/-! ## 一、约束级标签 -/

def cExpr : ℕ := 5
def cDistEq : ℕ := 6
def cSamePoint : ℕ := 7
def cPerp : ℕ := 8

@[simp] theorem cExpr_eq : cExpr = 5 := rfl
@[simp] theorem cDistEq_eq : cDistEq = 6 := rfl
@[simp] theorem cSamePoint_eq : cSamePoint = 7 := rfl
@[simp] theorem cPerp_eq : cPerp = 8 := rfl

/-! ## 二、编码 -/

/-- **编码一个约束。** 每个构造子一个标签，坐标用 `inl`，表达式递归编码。 -/
def encCon : EqConstraint n → List EqTok
  | .expr e => Sum.inl cExpr :: encExpr e
  | .distEq a b d => Sum.inl cDistEq :: Sum.inl a :: Sum.inl b :: encExpr d
  | .samePoint a b => [Sum.inl cSamePoint, Sum.inl a, Sum.inl b]
  | .perpendicular a b c e =>
      [Sum.inl cPerp, Sum.inl a, Sum.inl b, Sum.inl c, Sum.inl e]

/-- 编码长度的计算式。 -/
def encLenC : EqConstraint n → ℕ
  | .expr e => 1 + encLenE e
  | .distEq _ _ d => 3 + encLenE d
  | .samePoint _ _ => 3
  | .perpendicular _ _ _ _ => 5

theorem encCon_length (c : EqConstraint n) : (encCon (n := n) c).length = encLenC c := by
  cases c with
  | expr e =>
      show (Sum.inl cExpr :: encExpr e).length = 1 + encLenE e
      simp only [List.length_cons, encExpr_length]
      omega
  | distEq a b d =>
      show (Sum.inl cDistEq :: Sum.inl a :: Sum.inl b :: encExpr d).length = 3 + encLenE d
      simp only [List.length_cons, encExpr_length]
      omega
  | samePoint a b => rfl
  | perpendicular a b c e => rfl

/-! ## 三、解码器 -/

/-- `decCon`'s `expr` body. -/
def decExprBody (rest : List EqTok) : Option (EqConstraint n × ℕ) :=
  match decExpr (n := n) (rest.length + 1) rest with
  | some (e, k) => some (.expr e, 1 + k)
  | none => none

/-- `decCon`'s `distEq` body. -/
def decDistEqBody (rest : List EqTok) : Option (EqConstraint n × ℕ) :=
  match rest with
  | Sum.inl a :: Sum.inl b :: rest' =>
      (match decExpr (n := n) (rest'.length + 1) rest' with
       | some (d, k) => some (.distEq a b d, 3 + k)
       | none => none)
  | _ => none

/-- `decCon`'s `samePoint` body. -/
def decSamePointBody (rest : List EqTok) : Option (EqConstraint n × ℕ) :=
  match rest with
  | Sum.inl a :: Sum.inl b :: _ => some (.samePoint a b, 3)
  | _ => none

/-- `decCon`'s `perpendicular` body. -/
def decPerpBody (rest : List EqTok) : Option (EqConstraint n × ℕ) :=
  match rest with
  | Sum.inl a :: Sum.inl b :: Sum.inl c :: Sum.inl e :: _ =>
      some (.perpendicular a b c e, 5)
  | _ => none

/-- **解码一个约束**：标签决定构造子，表达式交给 `decExpr`。

fuel 取 `rest.length + 1`——因为 `encLenE e ≤ (encExpr e).length`，剩余长度总是够。 -/
def decCon : ℕ → List EqTok → Option (EqConstraint n × ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, Sum.inl t :: rest =>
      if t = cExpr then decExprBody (n := n) rest
      else if t = cDistEq then decDistEqBody (n := n) rest
      else if t = cSamePoint then decSamePointBody (n := n) rest
      else if t = cPerp then decPerpBody (n := n) rest
      else none
  | _ + 1, _ => none

/-! ## 四、fuel 够用的引理 -/

/-- **`encLenE e` 不超过拼接后的长度**：这是 `decCon` 用 `rest.length + 1` 作 fuel 的依据。 -/
theorem encLenE_le_length (e : GeoExpr n) (rest : List EqTok) :
    encLenE e ≤ (encExpr e ++ rest).length := by
  rw [List.length_append, ← encExpr_length (n := n) e]
  omega

/-! ## 五、往返 -/

/-- **`expr` 往返**：标签 + 一个表达式。 -/
theorem decCon_expr (e : GeoExpr n) (suffix : List EqTok) (k : ℕ) :
    decCon (n := n) (k + 1)
      (encCon (n := n) (.expr e) ++ suffix) = some (.expr e, 1 + encLenE e) := by
  show decCon (n := n) (k + 1)
    (Sum.inl cExpr :: (encExpr e ++ suffix)) = some (.expr e, 1 + encLenE e)
  rw [decCon.eq_def]
  simp only [cExpr_eq, if_pos rfl]
  show decExprBody (n := n) (encExpr e ++ suffix) = some (.expr e, 1 + encLenE e)
  simp only [decExprBody]
  have hfuel : encLenE e ≤ (encExpr e ++ suffix).length + 1 := by
    have := encLenE_le_length (n := n) e suffix
    omega
  rw [decExpr_enc (n := n) e suffix ((encExpr e ++ suffix).length + 1) hfuel]

/-- **`samePoint` 往返**：标签 + 两个坐标，无表达式。 -/
theorem decCon_samePoint (a b : ℕ) (suffix : List EqTok) (k : ℕ) :
    decCon (n := n) (k + 1)
      (encCon (n := n) (.samePoint a b) ++ suffix) = some (.samePoint a b, 3) := by
  show decCon (n := n) (k + 1)
    (Sum.inl cSamePoint :: (Sum.inl a :: (Sum.inl b :: suffix))) =
    some (.samePoint a b, 3)
  rw [decCon.eq_def]
  simp only [cSamePoint_eq, cExpr_eq, cDistEq_eq]
  rw [if_neg (by norm_num : ¬(7 : ℕ) = 5)]
  rw [if_neg (by norm_num : ¬(7 : ℕ) = 6)]
  rw [if_pos trivial]
  show decSamePointBody (n := n) (Sum.inl a :: Sum.inl b :: suffix) =
    some (.samePoint a b, 3)
  simp only [decSamePointBody]

/-- **`perpendicular` 往返**：标签 + 四个坐标。 -/
theorem decCon_perp (a b c e : ℕ) (suffix : List EqTok) (k : ℕ) :
    decCon (n := n) (k + 1)
      (encCon (n := n) (.perpendicular a b c e) ++ suffix) =
      some (.perpendicular a b c e, 5) := by
  show decCon (n := n) (k + 1)
    (Sum.inl cPerp :: (Sum.inl a :: (Sum.inl b :: (Sum.inl c :: (Sum.inl e :: suffix))))) =
    some (.perpendicular a b c e, 5)
  rw [decCon.eq_def]
  simp only [cPerp_eq, cExpr_eq, cDistEq_eq, cSamePoint_eq]
  rw [if_neg (by norm_num : ¬(8 : ℕ) = 5)]
  rw [if_neg (by norm_num : ¬(8 : ℕ) = 6)]
  rw [if_neg (by norm_num : ¬(8 : ℕ) = 7)]
  rw [if_pos trivial]
  show decPerpBody (n := n) (Sum.inl a :: Sum.inl b :: Sum.inl c :: Sum.inl e :: suffix) =
    some (.perpendicular a b c e, 5)
  simp only [decPerpBody]

/-- **`distEq` 往返**：标签 + 两个坐标 + 一个表达式。 -/
theorem decCon_distEq (a b : ℕ) (d : GeoExpr n) (suffix : List EqTok) (k : ℕ) :
    decCon (n := n) (k + 1)
      (encCon (n := n) (.distEq a b d) ++ suffix) = some (.distEq a b d, 3 + encLenE d) := by
  show decCon (n := n) (k + 1)
    (Sum.inl cDistEq :: (Sum.inl a :: (Sum.inl b :: (encExpr d ++ suffix)))) =
    some (.distEq a b d, 3 + encLenE d)
  rw [decCon.eq_def]
  simp only [cDistEq_eq, cExpr_eq]
  rw [if_neg (by norm_num : ¬(6 : ℕ) = 5)]
  rw [if_pos trivial]
  show decDistEqBody (n := n) (Sum.inl a :: Sum.inl b :: (encExpr d ++ suffix)) =
    some (.distEq a b d, 3 + encLenE d)
  simp only [decDistEqBody]
  have hfuel : encLenE d ≤ (encExpr d ++ suffix).length + 1 := by
    have := encLenE_le_length (n := n) d suffix
    omega
  rw [decExpr_enc (n := n) d suffix ((encExpr d ++ suffix).length + 1) hfuel]

/-- **完整往返**：任意 `EqConstraint` 都能从它的 token 流还原。 -/
theorem decCon_enc (c : EqConstraint n) :
    ∀ (suffix : List EqTok) (fuel : ℕ), encLenC c ≤ fuel →
      decCon (n := n) fuel (encCon (n := n) c ++ suffix) = some (c, encLenC c) := by
  intro suffix fuel h
  cases c with
  | expr e =>
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [encLenC] at h; omega⟩
      exact decCon_expr e suffix k
  | distEq a b d =>
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [encLenC] at h; omega⟩
      exact decCon_distEq a b d suffix k
  | samePoint a b =>
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [encLenC] at h; omega⟩
      exact decCon_samePoint a b suffix k
  | perpendicular a b c e =>
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [encLenC] at h; omega⟩
      exact decCon_perp a b c e suffix k

/-- **无后缀形式**：编码后以足够的 fuel 解码，得到原约束。 -/
theorem decCon_enc_nil (c : EqConstraint n) :
    decCon (n := n) (encLenC c) (encCon (n := n) c) = some (c, encLenC c) := by
  have h := decCon_enc c [] (encLenC c) (Nat.le_refl _)
  rwa [List.append_nil] at h


end EqConstraintToken

end Lattice.Geo
