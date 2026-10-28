/-
# 多约束数据集的 tokenizer：`Data = List (EqConstraint n)`

## 0. 本节补什么

第 150 轮把 `geoLadder` 的 `l1l2` 换成了真 tokenizer（`EqConstraintTokens`），但为了不改变
`Data` 的类型，把 `Data` 取成 `EqConstraint n`——**一个数据项就是一个约束**，于是
`l0l1` 与 `l1l2` 是同一个映射。

**那让四跳都有内容，但「数据层」退化了。** 本节补上列表：

```
Data = List (EqConstraint n)     一个数据集是一串约束
Tok  = EqTok                      同一种 token
Sym  = EqConstraint n             一个符号模型是一个约束
```

## 1. 两次失败，两个不同的原因

**第 151 轮**用 `decList (fuel) (ts)`，内层 `match ts`：

```lean
match ts with
| [] => some []
| _ => match fuel with ...
```

**`decList [] fuel` 不是 `rfl`。** Lean 的方程编译器把「第二个参数匹配 `[]`」与
「第一个参数匹配 `0` / `f+1`」**合并成一个匹配矩阵**，所以 `[]` 分支仍然对 `fuel` 有要求。

**第 153 轮第一次尝试**改用单参数递归 + `termination_by ts => ts.length`：

**`decList []` 仍然不是 `rfl`**——**因为 `termination_by` 会产生 well-founded recursion，
而 well-founded 定义不生成方程引理。**

## 2. 正确的设计：结构递归在 fuel 上，`[]` 两种 fuel 都写出来

```lean
def decList : ℕ → List EqTok → Option (List (EqConstraint n))
  | 0,       []              => some []
  | 0,       _               => none
  | _ + 1,   []              => some []
  | fuel + 1, Sum.inl k :: rest => ...
  | _ + 1,   Sum.inr _ :: _  => none
```

**这样**：
- `decList fuel [] = some []` 对每个 `fuel` 都成立，`cases fuel` 后两个分支都是 `rfl`
- **递归是结构递归（`fuel + 1` → `fuel`），Lean 不需要 `termination_by`**

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `decList_nil` | **对任意 fuel，空流解码为空表** |
| `encCon_head_inl` | **`encCon` 的首 token 是 `inl`**（解码器模式匹配的前提） |
| `drop_encCon` | 去掉一个编码的长度后剩后缀 |
| **`decList_enc`** | **列表往返** |
| **`eqConstraintListTokenizer`** | **`Tokenizer (List (EqConstraint n)) EqTok`** |

## 4. 边界

- 本节**不改** `geoLadder` 的 `Data`；把 `Data` 换回列表需要同时改类型签名与相关定理，
  是接线的一步（见 `GeoLadder` 的 §3）。
- **列表解码需要 `fuel`**，因为 `decCon` 的消费数不影响终止性——终止性靠 fuel 递减。
  **这一点与单个约束的解码不同**（那里 fuel 由 `ts.length` 推出）。
-/
import Mathlib
import Lattice.Domains.EqConstraintTokens

open Lattice.Geo
open Lattice.Geo.EqTok
open Lattice.Geo.EqTokRoundtrip
open Lattice.Geo.EqConstraintToken

namespace Lattice.Geo

namespace EqConstraintListTokens

variable {n : ℕ}

/-- **列表的编码**：顺序拼接每个约束的编码。 -/
def encList : List (EqConstraint n) → List EqTok
  | [] => []
  | c :: cs => encCon c ++ encList cs

/-- **列表的解码**：fuel 上的结构递归。

`[]` 分支对 `0` 与 `f+1` 各写一次，**这是 `decList_nil` 能被 `rfl` 证明的原因**。 -/
def decList : ℕ → List EqTok → Option (List (EqConstraint n))
  | 0, [] => some []
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, Sum.inl k :: rest =>
      (match decCon (n := n) ((Sum.inl k :: rest).length + 1) (Sum.inl k :: rest) with
       | some (c, used) => (decList fuel ((Sum.inl k :: rest).drop used)).map (c :: ·)
       | none => none)
  | _ + 1, Sum.inr _ :: _ => none

/-- **空流解码为空表，对任意 fuel。** -/
theorem decList_nil (fuel : ℕ) : decList (n := n) fuel [] = some [] := by
  cases fuel with
  | zero => rfl
  | succ f => rfl

/-- **`encCon c` 的首 token 是 `Sum.inl`。** -/
theorem encCon_head_inl (c : EqConstraint n) :
    ∃ (t : ℕ) (tl : List EqTok), encCon (n := n) c = Sum.inl t :: tl := by
  cases c with
  | expr e => exact ⟨_, _, rfl⟩
  | distEq a b d => exact ⟨_, _, rfl⟩
  | samePoint a b => exact ⟨_, _, rfl⟩
  | perpendicular a b c e => exact ⟨_, _, rfl⟩

/-- **去掉一个编码的长度后剩后缀。** -/
theorem drop_encCon (c : EqConstraint n) (rest : List EqTok) :
    (encCon c ++ rest).drop (encLenC c) = rest := by
  rw [← encCon_length (n := n) c]
  simp

/-- **`encCon c` 非空。** -/
theorem encCon_ne_nil (c : EqConstraint n) : encCon (n := n) c ≠ [] := by
  cases c with
  | expr e => exact List.cons_ne_nil _ _
  | distEq a b d => exact List.cons_ne_nil _ _
  | samePoint a b => exact List.cons_ne_nil _ _
  | perpendicular a b c e => exact List.cons_ne_nil _ _

/-- **`encList` 至少和列表本身一样长**：每个 `encCon c` 非空。 -/
theorem encList_length_ge (cs : List (EqConstraint n)) :
    cs.length ≤ (encList (n := n) cs).length := by
  induction cs with
  | nil => simp only [encList, List.length_nil, Nat.le_refl]
  | cons c cs ih =>
      show (c :: cs).length ≤ (encCon c ++ encList cs).length
      rw [List.length_cons, List.length_append]
      have hc : 0 < (encCon (n := n) c).length := by
        have := encCon_ne_nil c
        cases h : encCon (n := n) c with
        | nil => exact absurd h this
        | cons t tl => simp only [List.length_cons]; omega
      omega

/-- **列表往返。** -/
theorem decList_enc (cs : List (EqConstraint n)) (k : ℕ) :
    decList (n := n) (cs.length + k) (encList (n := n) cs) = some cs := by
  induction cs generalizing k with
  | nil =>
      show decList (n := n) (0 + k) [] = some []
      rw [Nat.zero_add]
      exact decList_nil k
  | cons c cs ih =>
      show decList (n := n) ((c :: cs).length + k) (encCon c ++ encList cs) = some (c :: cs)
      have hlen : (c :: cs).length + k = cs.length + k + 1 := by
        simp only [List.length_cons]; omega
      rw [hlen]
      obtain ⟨tag, tl, htag⟩ := encCon_head_inl c
      rw [htag, List.cons_append]
      show (match decCon (n := n) ((Sum.inl tag :: (tl ++ encList cs)).length + 1)
              (Sum.inl tag :: (tl ++ encList cs)) with
            | some (c', used) =>
                (decList (n := n) (cs.length + k)
                  ((Sum.inl tag :: (tl ++ encList cs)).drop used)).map (c' :: ·)
            | none => none) = some (c :: cs)
      rw [← List.cons_append]
      rw [← htag]
      rw [decCon_enc c (encList cs) ((encCon c ++ encList cs).length + 1) (by
        simp only [List.length_append, ← encCon_length (n := n) c]
        omega)]
      simp only []
      rw [drop_encCon c (encList cs)]
      rw [ih k]
      rfl

/-- **多约束数据集的 tokenizer**：`Data = List (EqConstraint n)`，`Tok = EqTok`。

fuel 取 token 列表长度：至少等于约束个数减一，而 `decList` 每个约束消耗一单位 fuel。 -/
def eqConstraintListTokenizer :
    Lattice.Lift.Tokenizer (List (EqConstraint n)) EqTok where
  encode := encList
  decode := fun ts => decList ts.length ts
  roundtrip := fun cs => by
    show decList (n := n) (encList (n := n) cs).length (encList (n := n) cs) = some cs
    obtain ⟨k, hk⟩ : ∃ k, (encList (n := n) cs).length = cs.length + k :=
      ⟨(encList (n := n) cs).length - cs.length,
       by have := encList_length_ge cs; omega⟩
    rw [hk]
    exact decList_enc cs k

/-- **它真的编码多于一个约束**：两个约束的编码是两个编码的拼接。 -/
theorem eqConstraintListTokenizer_two (a b c d : ℕ) :
    (eqConstraintListTokenizer (n := n)).encode [.samePoint a b, .samePoint c d] =
      ([Sum.inl cSamePoint, Sum.inl a, Sum.inl b] ++
       [Sum.inl cSamePoint, Sum.inl c, Sum.inl d]) := rfl

end EqConstraintListTokens

end Lattice.Geo
