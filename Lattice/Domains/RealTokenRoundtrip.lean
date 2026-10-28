/-
# `decExpr` 的完整往返：五构造子全部成立

## 0. 本节补什么

第 147 轮交付了 `RealToken`：`EqTok := ℕ ⊕ ℝ` 的编码器、带 fuel 的解码器，以及**两个叶子往返**
（坐标 3 token、常量 2 token）。它明确记录了三元分支（`tAdd` / `tSub` / `tMul`）**已实现但往返未证**。

本节把这三条补上，并给出完整定理。

## 1. 与 `ConstraintTokenizer` 那次的不同

第 144 轮 `ConstraintTokenizer.dec_enc_append` 的归纳里，`cases ha' : enc e` 之后就够了。

**`decExpr` 不行**：它的第一个模式是 `Sum.inl t :: d :: rest`，**要求第一个 token 是 `inl`**。
而 `cases` 只给出「是 cons」，不给「首元素是 `inl`」。

**解法**：用 `encExpr_head_inl`（第 147 轮已有的引理）先取出 `Sum.inl t :: tl` 这个形态，
再走第 144 轮的两条 ★ 行。

## 2. 三条辅助引理

| 引理 | 内容 |
|:--|:--|
| `decExpr_add_step` / `_sub_step` / `_mul_step` | 方程引理，**第二 token 任意** |
| `encLenE_ge_two` | fuel 下界 |
| `drop_encExpr` | 去掉一个编码的长度后剩后缀 |

**方程引理的证明用 `decExpr.eq_def` + `norm_num` + `rfl`**——与 `ConstraintTokenizer` 那次
用 `dec.eq_def` 完全同构。**`rw [decExpr]` 不行**（那会展开所有 `if` 分支并留下不可达的 `match`
义务）。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| **`decExpr_enc`** | **对任意 `GeoExpr` 与任意后缀的精确消费引理** |
| **`decExpr_enc_nil`** | **`decExpr (encLenE e) (encExpr e) = some (e, encLenE e)`** |

## 4. 边界

- 本节只做 `GeoExpr`，**不含 `EqConstraint` 的四个构造子标签**。
- **`geoLadder` 的 `l1l2` 仍未换成这个 tokenizer**——见 §5 的说明。
- `EqTok` 含 `ℝ`，所以**不能对它用 `DecidableEq` 相关的策略**；本节所有证明都绕开了这一点。

## 5. 为什么 `geoLadder` 还没换

`Ladder.l1l2 : Tokenizer Sym Tok` 里 `Tok` 是**单个 token 类型**。本节提供的是
`GeoExpr ⇄ List EqTok`。要接进 `Ladder`，还需要把 `EqConstraint` 的四个构造子也编码
（每个一个标签），并把 `l1l2` 的往返定理补上。**那是下一步，不是本节。**
-/
import Mathlib
import Lattice.Domains.RealToken

open Lattice.Geo
open Lattice.Geo.EqTok

namespace Lattice.Geo

namespace EqTokRoundtrip

variable {n : ℕ}


variable {n : ℕ}

/-- Equation lemma for the add branch, arbitrary second token. -/
theorem decExpr_add_step (k : ℕ) (d : EqTok) (rest : List EqTok) :
    decExpr (n := n) (k + 1) (Sum.inl tAdd :: d :: rest) =
      (match decExpr (n := n) k (d :: rest) with
       | some (x, c₁) =>
           match decExpr (n := n) k ((d :: rest).drop c₁) with
           | some (y, c₂) => some (.add x y, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rw [decExpr.eq_def]
  simp only [tAdd_eq, tSub_eq, tMul_eq, tCoord_eq, tConst_eq]
  norm_num
  rfl

/-- Equation lemma for the sub branch, arbitrary second token. -/
theorem decExpr_sub_step (k : ℕ) (d : EqTok) (rest : List EqTok) :
    decExpr (n := n) (k + 1) (Sum.inl tSub :: d :: rest) =
      (match decExpr (n := n) k (d :: rest) with
       | some (x, c₁) =>
           match decExpr (n := n) k ((d :: rest).drop c₁) with
           | some (y, c₂) => some (.sub x y, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rw [decExpr.eq_def]
  simp only [tAdd_eq, tSub_eq, tMul_eq, tCoord_eq, tConst_eq]
  norm_num
  rfl

/-- Equation lemma for the mul branch, arbitrary second token. -/
theorem decExpr_mul_step (k : ℕ) (d : EqTok) (rest : List EqTok) :
    decExpr (n := n) (k + 1) (Sum.inl tMul :: d :: rest) =
      (match decExpr (n := n) k (d :: rest) with
       | some (x, c₁) =>
           match decExpr (n := n) k ((d :: rest).drop c₁) with
           | some (y, c₂) => some (.mul x y, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rw [decExpr.eq_def]
  simp only [tAdd_eq, tSub_eq, tMul_eq, tCoord_eq, tConst_eq]
  norm_num
  rfl

/-- `encLenE e ≥ 2`. -/
theorem encLenE_ge_two (e : GeoExpr n) : 2 ≤ encLenE e := by
  induction e with
  | coord p axis => show 2 ≤ 3; omega
  | const c => show 2 ≤ 2; exact Nat.le_refl 2
  | add a b iha ihb => show 2 ≤ 1 + encLenE a + encLenE b; omega
  | sub a b iha ihb => show 2 ≤ 1 + encLenE a + encLenE b; omega
  | mul a b iha ihb => show 2 ≤ 1 + encLenE a + encLenE b; omega

/-- Dropping an encoding's length from `encExpr e ++ X` leaves `X`. -/
theorem drop_encExpr (e : GeoExpr n) (X : List EqTok) :
    (encExpr e ++ X).drop (encLenE e) = X := by
  rw [← encExpr_length (n := n) e]
  simp

/-- **The full round-trip, all five constructors.**

Same shape as `ConstraintTokenizer.dec_enc_append`, with one extra step: `decExpr`'s patterns need
the first token to be `Sum.inl`, so the induction must extract that with `encExpr_head_inl` before
the equation lemma can fire. -/
theorem decExpr_enc (e : GeoExpr n) :
    ∀ (suffix : List EqTok) (fuel : ℕ), encLenE e ≤ fuel →
      decExpr (n := n) fuel (encExpr e ++ suffix) = some (e, encLenE e) := by
  induction e with
  | coord p axis =>
      intro suffix fuel h
      simp only [encLenE] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
      show decExpr (n := n) (f + 3)
        ((Sum.inl tCoord :: Sum.inl p :: Sum.inl axis.val :: []) ++ suffix) =
        some (.coord p axis, 3)
      simp only [List.cons_append, List.nil_append]
      rw [show (f + 3) = ((f + 1) + 1) + 1 from rfl]
      rw [decExpr.eq_def]
      simp only [tAdd_eq, tSub_eq, tMul_eq, tCoord_eq, tConst_eq]
      norm_num
  | const c =>
      intro suffix fuel h
      simp only [encLenE] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
      show decExpr (n := n) (f + 2)
        ((Sum.inl tConst :: Sum.inr c :: []) ++ suffix) = some (.const c, 2)
      simp only [List.cons_append, List.nil_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [decExpr.eq_def]
      simp only [tAdd_eq, tSub_eq, tMul_eq, tCoord_eq, tConst_eq]
      norm_num
  | add a b iha ihb =>
      intro suffix fuel h
      simp only [encLenE] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by
        have h1 := encLenE_ge_two a; have h2 := encLenE_ge_two b; omega⟩
      have ha : encLenE a ≤ f + 1 := by omega
      have hb : encLenE b ≤ f + 1 := by omega
      obtain ⟨t, tl, ht⟩ := encExpr_head_inl a
      show decExpr (n := n) (f + 2)
        ((Sum.inl tAdd :: (encExpr a ++ encExpr b)) ++ suffix) =
        some (.add a b, 1 + encLenE a + encLenE b)
      rw [List.cons_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [List.append_assoc]
      rw [ht]
      rw [List.cons_append]
      rw [decExpr_add_step (n := n) (k := f + 1) (d := Sum.inl t)
            (rest := tl ++ (encExpr b ++ suffix))]
      rw [show (Sum.inl t :: (tl ++ (encExpr b ++ suffix))) =
            ((Sum.inl t :: tl) ++ (encExpr b ++ suffix)) from rfl]
      rw [← ht]
      rw [iha (encExpr b ++ suffix) (f + 1) ha]
      simp only []
      rw [drop_encExpr a (encExpr b ++ suffix)]
      rw [ihb suffix (f + 1) hb]
  | sub a b iha ihb =>
      intro suffix fuel h
      simp only [encLenE] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by
        have h1 := encLenE_ge_two a; have h2 := encLenE_ge_two b; omega⟩
      have ha : encLenE a ≤ f + 1 := by omega
      have hb : encLenE b ≤ f + 1 := by omega
      obtain ⟨t, tl, ht⟩ := encExpr_head_inl a
      show decExpr (n := n) (f + 2)
        ((Sum.inl tSub :: (encExpr a ++ encExpr b)) ++ suffix) =
        some (.sub a b, 1 + encLenE a + encLenE b)
      rw [List.cons_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [List.append_assoc]
      rw [ht]
      rw [List.cons_append]
      rw [decExpr_sub_step (n := n) (k := f + 1) (d := Sum.inl t)
            (rest := tl ++ (encExpr b ++ suffix))]
      rw [show (Sum.inl t :: (tl ++ (encExpr b ++ suffix))) =
            ((Sum.inl t :: tl) ++ (encExpr b ++ suffix)) from rfl]
      rw [← ht]
      rw [iha (encExpr b ++ suffix) (f + 1) ha]
      simp only []
      rw [drop_encExpr a (encExpr b ++ suffix)]
      rw [ihb suffix (f + 1) hb]
  | mul a b iha ihb =>
      intro suffix fuel h
      simp only [encLenE] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by
        have h1 := encLenE_ge_two a; have h2 := encLenE_ge_two b; omega⟩
      have ha : encLenE a ≤ f + 1 := by omega
      have hb : encLenE b ≤ f + 1 := by omega
      obtain ⟨t, tl, ht⟩ := encExpr_head_inl a
      show decExpr (n := n) (f + 2)
        ((Sum.inl tMul :: (encExpr a ++ encExpr b)) ++ suffix) =
        some (.mul a b, 1 + encLenE a + encLenE b)
      rw [List.cons_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [List.append_assoc]
      rw [ht]
      rw [List.cons_append]
      rw [decExpr_mul_step (n := n) (k := f + 1) (d := Sum.inl t)
            (rest := tl ++ (encExpr b ++ suffix))]
      rw [show (Sum.inl t :: (tl ++ (encExpr b ++ suffix))) =
            ((Sum.inl t :: tl) ++ (encExpr b ++ suffix)) from rfl]
      rw [← ht]
      rw [iha (encExpr b ++ suffix) (f + 1) ha]
      simp only []
      rw [drop_encExpr a (encExpr b ++ suffix)]
      rw [ihb suffix (f + 1) hb]


/-- **Every `GeoExpr` round-trips** through the real-carrying token stream. -/
theorem decExpr_enc_nil (e : GeoExpr n) :
    decExpr (n := n) (encLenE e) (encExpr e) = some (e, encLenE e) := by
  have h := decExpr_enc e [] (encLenE e) (Nat.le_refl _)
  rwa [List.append_nil] at h


end EqTokRoundtrip

end Lattice.Geo
