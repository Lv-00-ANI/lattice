/-
# `layerOfListFull` 的逆：把权重读回符号

## 0. 设计

编码器从 `s[n*i + j]` 读 `W i j`、从 `s[n*n + j]` 读 `b j`。**逆向要产出第 `k` 项是这些值的列表。**

**用除法索引读 `W` 让算术塌缩**：

```lean
listOfLayer L := [ L.W (k/n) (k%n) | k < n*n ] ++ [ L.b j | j < n ]
```

**那么系数块的第 `k` 项是 `s[(k/n)*n + (k%n)] = s[k]`，由 `Nat.div_mul_add_mod`——
一次重写，不需要对行列做双重归纳。**

**这是第 165 轮「缺逆」的直接补法**：那轮证明了 `layerOfList` 丢弃列下标、因此不是单射；
本节对**满宽**版本给出逆。

## 1. 主定理

| 定理 | 内容 |
|:--|:--|
| `listOfLayer` | **逆的定义**：系数按行主序（除法索引），然后偏置 |
| **`listOfLayer_length`** | **长度是 `n*n + n`** |
| **`listOfLayer_W`** | **系数位置 `k` 读出 `W (k/n) (k%n)`** |
| **`listOfLayer_b`** | **偏置位置 `n*n + j` 读出 `b j`** |

**三条合起来说明：逆对每个分量都读对了。**

## 2. 往返（第 168 轮补上）

**`roundtrip`：`listOfLayer hn (layerOfListFull s) = s`，前提 `s.length = n*n + n`。**

第 166 轮记录「往返未证」，理由是 `List.getElem` 的证明无关性。**那个判断是对的，但绕过去的办法很简单**：
不走 `listOfLayer_W`/`_b`（它们把下标证明写死），而是直接展开 `listOfLayer`，用
`List.getElem_append_left`/`_right`——**这两条的证明参数是隐式的**，于是 `List.ext_getElem`
提供的证明自然匹配。

两半各归约成一条算术：
- 系数半：`(k/n)*n + k%n = k`（`Nat.div_add_mod` 加 `Nat.mul_comm`）
- 偏置半：`n*n + (k - n*n) = k`（`Nat.add_sub_cancel'`）

**一个次序陷阱**：`List.length_ofFn` 不能在减法还当下标时重写——那会改变 `getElem` 的下标类型，
motive 就不再 type-correct。必须先把减法移进 `getD`，再重写长度。

## 3. 边界（必须明说）

- **`listOfLayer` 需要 `hn : 0 < n`**，因为 `Fin n` 要可居留、`k % n` 要有意义。
  `n = 0` 时 `AffineLayer (Fin 0)` 是空类型，无需逆。
- **往返带长度前提** `s.length = n*n + n`。用 `List ℝ` 就必须带它；若把符号侧改成
  `Fin (n*n+n) → ℝ`，长度进类型，前提可以去掉。**本节选择保留 `List ℝ`**，因为上层的
  token 层就是列表，换成定长函数会让 `l1l2` 失去意义。
- **`layerOfListFull` 与 `listOfLayer` 都还没有接进 `WeightLadderN`**：本节只提供配对与往返，
  替换 `l2l3` 与重证 `act_zero_of_all_zero` 是下一步。
- 本节**不改** `WeightLadderN` 与 `WeightLadderFullWidth` 的任何既有定理。
-/

import Mathlib
import Lattice.Lift.WeightLadderFullWidth

namespace FullWidth

open Lattice.Core

variable {n : ℕ}

/-- **The inverse**: coefficients in row-major order via division indexing, then the biases. -/
noncomputable def listOfLayer (hn : 0 < n) (L : AffineLayer (Fin n)) : List ℝ :=
  (List.ofFn (fun k : Fin (n * n) =>
      L.W ⟨k.val / n, Nat.div_lt_of_lt_mul k.isLt⟩ ⟨k.val % n, Nat.mod_lt _ hn⟩)) ++
    (List.ofFn (fun j : Fin n => L.b j))

/-- **Length of the inverse is `n*n + n`.** -/
theorem listOfLayer_length (hn : 0 < n) (L : AffineLayer (Fin n)) :
    (listOfLayer hn L).length = n * n + n := by
  unfold listOfLayer
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

/-- **A coefficient position reads the right entry.**

`k` indexes the row-major block; `k / n` is the row and `k % n` the column, and the encoder stored
exactly `W (k/n) (k%n)` at `(k/n)*n + (k%n) = k`. -/
theorem listOfLayer_W (hn : 0 < n) (L : AffineLayer (Fin n)) (k : Fin (n * n)) :
    (listOfLayer hn L)[k.val]'(by rw [listOfLayer_length]; omega) =
      L.W ⟨k.val / n, Nat.div_lt_of_lt_mul k.isLt⟩ ⟨k.val % n, Nat.mod_lt _ hn⟩ := by
  unfold listOfLayer
  rw [List.getElem_append_left (by rw [List.length_ofFn]; exact k.isLt)]
  exact List.getElem_ofFn _ _ _

/-- **A bias position reads the right entry.** -/
theorem listOfLayer_b (hn : 0 < n) (L : AffineLayer (Fin n)) (j : Fin n) :
    (listOfLayer hn L)[n * n + j.val]'(by rw [listOfLayer_length]; omega) = L.b j := by
  unfold listOfLayer
  rw [List.getElem_append_right (by rw [List.length_ofFn]; exact Nat.le_add_right _ _)]
  simp only [List.length_ofFn]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem_ofFn _ _ _


/-- **The round-trip**: the inverse recovers a list of the right length exactly.

Both halves go through `List.getElem_append_left/right` rather than through `listOfLayer_W`/`_b`,
because those state a FIXED index proof while `List.ext_getElem` supplies a different one. The append
lemmas take their proof argument implicitly, which is what lets the rewrite go through -- going through
the fixed-proof versions is where round 166 got stuck.

The coefficient half reduces to `(k/n)*n + k%n = k` (`Nat.div_add_mod` after `Nat.mul_comm`); the bias
half to `n*n + (k - n*n) = k` (`Nat.add_sub_cancel'`).
-/
theorem roundtrip (hn : 0 < n) (s : List ℝ) (hlen : s.length = n * n + n) :
    listOfLayer hn (layerOfListFull (n := n) s) = s := by
  apply List.ext_getElem
  · rw [listOfLayer_length, hlen]
  · intro k h1 h2
    unfold listOfLayer
    rcases Nat.lt_or_ge k (n * n) with hk | hk
    · rw [List.getElem_append_left (i := k) (as := List.ofFn (fun k : Fin (n * n) =>
          (layerOfListFull (n := n) s).W ⟨k.val / n, Nat.div_lt_of_lt_mul k.isLt⟩
            ⟨k.val % n, Nat.mod_lt _ hn⟩))
        (by rw [List.length_ofFn]; exact hk)]
      rw [List.getElem_ofFn, layerOfListFull_W]
      rw [Nat.mul_comm (k / n) n, Nat.div_add_mod k n]
      exact List.getD_eq_getElem _ _ h2
    · rw [List.getElem_append_right (i := k) (as := List.ofFn (fun k : Fin (n * n) =>
          (layerOfListFull (n := n) s).W ⟨k.val / n, Nat.div_lt_of_lt_mul k.isLt⟩
            ⟨k.val % n, Nat.mod_lt _ hn⟩))
        (by rw [List.length_ofFn]; exact hk)]
      rw [List.getElem_ofFn, layerOfListFull_b]
      -- reduce the `Fin` coercion `↑⟨k - …, _⟩` to the plain index before touching `length`
      simp only [Fin.val_mk]
      -- `List.length_ofFn` must NOT be rewritten while the subtraction is still an index: that
      -- changes the type of the `getElem` and the motive stops being type correct. By here the
      -- subtraction has moved inside `getD`, where rewriting is safe.
      rw [List.length_ofFn, Nat.add_sub_cancel' hk]
      exact List.getD_eq_getElem _ _ h2
end FullWidth
