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

## 2. 边界（必须明说）

- **完整往返 `listOfLayer (layerOfListFull s) = s` 未证。** 它需要处理
  `List.getElem` 的**证明无关性**：`listOfLayer_W` 给出的下标证明与
  `List.ext_getElem` 提供的不同，而 `rw` 不会自动跨过这一点。**这是机械适配，不是数学困难**，
  但如果不在同一节里做完，往返就不能算陈述。
- **`listOfLayer` 需要 `hn : 0 < n`**，因为 `Fin n` 要可居留、`k % n` 要有意义。
  `n = 0` 时 `AffineLayer (Fin 0)` 是空类型，无需逆。
- **`layerOfListFull` 与 `listOfLayer` 都还没有接进 `WeightLadderN`**：本节只提供配对，
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

end FullWidth
