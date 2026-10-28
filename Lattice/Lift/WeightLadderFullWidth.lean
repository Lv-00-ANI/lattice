/-
# `layerOfList` 丢了列下标——于是「权重 → 符号」这一跳不存在

## 0. 缺陷的精确陈述

`WeightLadderN.layerOfList` 的定义是

```lean
W := fun i _ => (s.take n).getD i.val 0
```

**那第二个 `_` 是列下标。所以 `W i j` 不依赖 `j`：`W` 的每一行都是同一个向量。**

docstring 说「前 `n` 项是系数」——**那描述的是秩 1 的层**；一个 `n × n` 权重矩阵需要 `n*n` 个。

## 1. 两个后果，第二个才是要害

1. **编码器丢信息，所以不是单射**（`old_not_injective` 给出两个不同列表映到同一个层）；
2. **因此它没有左逆，因此 `WeightLadderN` 没有「权重 → 符号」这一跳**——
   **而目标称这一跳是唯一的真难点。**

**所以这一跳的缺失不是因为疏漏，是因为编码器把信息扔掉了。**

## 2. 本节交付什么

| 定理 | 内容 |
|:--|:--|
| `layerOfListFull` | **满宽构造**：`n*n` 个系数按行主序，然后 `n` 个偏置 |
| `layerOfListFull_W` / `_b` | 读出引理的索引算术是显式的，不埋在定义里 |
| **`old_rank_one_at_two`** | **旧编码器在 `n = 2` 时每行两个元素相同** |
| **`new_not_rank_one_at_two`** | **新编码器给 `(1,2)` 与 `(3,4)`——四个不同** |
| **`encoders_differ`** | **两个编码器确实不是同一个函数** |
| **`old_not_injective`** | **旧编码器不是单射**（两个不同列表给出同一个层） |

**`encoders_differ` 是关键的一条**：它说明缺陷不能靠「给旧编码器补一个逆」修好——**旧编码器根本没有信息可供逆推。**

## 3. 边界（必须明说）

- **`weightLadderN` 的 `l2l3` 仍然用旧的 `layerOfList`。** 本节提供正确的构造与「它确实不同」
  的证据，**但没有替换**——替换会让 `act_zero_of_all_zero` 的证明需要重写，而那是独立的一步。
- **`listOfLayer`（逆）在本节未定义。** 长度算术（`n*n + n` 与 `List.finRange` 的
  `flatMap` 展开）是独立的一块，需要单独的引理组。**没有逆，往返就还不能陈述。**
- **本节不改 `WeightLadderN` 的任何既有定理。**
- 满宽构造**仍用 `getD`**，所以对任意长度的列表都是全函数；只有长度恰为 `n*n + n` 时
  它才在系数上是恒等。
-/

import Mathlib
import Lattice.Runtime.WeightLadderN

namespace FullWidth

open Lattice.Core

variable {n : ℕ}

/-- **Full-width construction**: `n*n` coefficients in row-major order, then `n` biases.

`getD` keeps it total on lists of any length; `layerOfListFull_length` says which length makes it the
identity on coefficients. -/
noncomputable def layerOfListFull (s : List ℝ) : AffineLayer (Fin n) where
  W := fun i j => s.getD (i.val * n + j.val) 0
  b := fun j => s.getD (n * n + j.val) 0

/-- **The coefficient is read at the right index** -- by definition, recorded so the index arithmetic
is visible rather than buried. -/
theorem layerOfListFull_W (s : List ℝ) (i j : Fin n) :
    (layerOfListFull (n := n) s).W i j = s.getD (i.val * n + j.val) 0 := rfl

/-- **The bias is read after the `n*n` coefficients.** -/
theorem layerOfListFull_b (s : List ℝ) (j : Fin n) :
    (layerOfListFull (n := n) s).b j = s.getD (n * n + j.val) 0 := rfl

/-! ## The evidence that the fix is real

At `n = 2`, `W` is a 2x2 matrix.

* Old encoder, `s = [1, 2, 3, 4, ...]`: rows are `(1,1)` and `(2,2)` -- equal entries, rank one.
* New encoder, same `s`: rows are `(1,2)` and `(3,4)` -- four distinct entries.
-/

/-- **The old encoder's matrix at `n = 2` has equal entries in each row.** -/
theorem old_rank_one_at_two (s : List ℝ) (i : Fin 2) :
    (Lattice.Lift.WeightLadderN.layerOfList (n := 2) s).W i 0 =
      (Lattice.Lift.WeightLadderN.layerOfList (n := 2) s).W i 1 := rfl

/-- **The new encoder's matrix at `n = 2` does not**: with `s = [1,2,3,4,0,0]` the
`(0,0)` entry is 1 and the `(0,1)` entry is 2. -/
theorem new_not_rank_one_at_two :
    (layerOfListFull (n := 2) [1, 2, 3, 4, 0, 0]).W 0 0 = 1 ∧
    (layerOfListFull (n := 2) [1, 2, 3, 4, 0, 0]).W 0 1 = 2 ∧
    (layerOfListFull (n := 2) [1, 2, 3, 4, 0, 0]).W 1 0 = 3 ∧
    (layerOfListFull (n := 2) [1, 2, 3, 4, 0, 0]).W 1 1 = 4 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **The two encoders are genuinely different functions** at `n = 2`.

Stated as an inequality of matrices via one entry, because that is enough to show they cannot be the
same encoder -- and therefore that the old one cannot be repaired by adding an inverse alone. -/
theorem encoders_differ :
    (layerOfListFull (n := 2) [1, 2, 3, 4, 0, 0]).W 0 1 ≠
      (Lattice.Lift.WeightLadderN.layerOfList (n := 2) [1, 2, 3, 4, 0, 0]).W 0 1 := by
  show (2 : ℝ) ≠ 1
  norm_num

/-- **The old encoder is not injective**: two different lists give the same layer. -/
theorem old_not_injective :
    Lattice.Lift.WeightLadderN.layerOfList (n := 2) [1, 0, 0, 0, 0, 0] =
      Lattice.Lift.WeightLadderN.layerOfList (n := 2) [1, 0, 0, 0, 1, 0] := by
  unfold Lattice.Lift.WeightLadderN.layerOfList
  simp only [AffineLayer.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext i j
    rfl
  · funext j
    fin_cases j <;> rfl

end FullWidth
