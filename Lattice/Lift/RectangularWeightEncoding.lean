/-
# 满宽编码器推广到**长方阵**：`LayerParams (Fin m) (Fin n)`

## 0. 为什么这是推广而不是重复

`Lift/WeightWadderFullWidth.lean` 与 `Lift/WeightWadderInverse.lean` 证的是
`AffineLayer (Fin n)`：`W : Fin n → Fin n → ℝ`，即**方阵**。而 `Core/Weight` 里更一般的结构是

```lean
structure LayerParams (m n : Type) where
  W : m → n → ℝ
  b : n → ℝ
```

**`m ≠ n` 是真实情形**：LLM 的层普遍不等宽（`d_model → d_ff → d_model`），
编码器的通用位置不该只对方阵成立。

**`m = n` 时本节的结果退化为方阵版**，所以这是严格推广，不是平行的一条路。

## 1. 编码与逆

方阵版的长度是 `n*n + n`；长方阵是 **`m*n + n`**。

| 分量 | 位置 |
|:--|:--|
| 系数 `W i j`（`i : Fin m`, `j : Fin n`） | `i*n + j`，覆盖 `[0, m*n)` |
| 偏置 `b j`（`j : Fin n`） | `m*n + j`，覆盖 `[m*n, m*n + n)` |

两段**不重叠且恰好覆盖** `[0, m*n + n)`——这就是可逆的原因，与方阵版同理。

**逆用除法索引**：`k` 处的系数是 `L.W (k/n) (k%n)`，因为 `(k/n)*n + (k%n) = k`
（`Nat.div_add_mod`）。

## 2. 一处从方阵版学来的细节

`k < m*n` 要推出 `k/n < m`。方阵版用 `Nat.div_lt_of_lt_mul`，但那个引理要求**除数在前**
（`a < b * c → a / b < c`），而这里 `Fin (m * n)` 把顺序定死成 `m * n`，
改写成 `n * m` 会改变 `k.isLt` 的类型（`k` 的类型依赖 `m * n`），`rw` 会报 motive 错误。

**改用 `Nat.div_lt_iff_lt_mul`**（`a / b < c ↔ 0 < b ∧ a < c * b`）：它不需要重排，
直接把 `hn` 与 `k.isLt` 接起来。**这是本节的唯一技术要点。**

## 3. 边界

- **`0 < n` 必需**（`Fin n` 要可居留、`k % n` 要有意义）。`n = 0` 时 `Fin 0` 是空类型。
- **`m` 可以是 `0`**：此时没有系数，只有 `n` 个偏置，长度 `0*n + n = n`，往返仍成立。
  这一条方阵版做不到（`m = n = 0` 时 `0 < n` 已经排除）。**这是本节比方阵版多出的一点。**
- 本节**不改** `WeightWadderFullWidth` / `WeightWadderInverse` 的任何既有定理。
  两者的关系写在 `layerOfListRect_eq_full_width`：`m = n` 时退化为 `layerOfListFull`。
-/
import Mathlib
import Lattice.Core.Weight
import Lattice.Lift.WeightLadderFullWidth

namespace Lattice.Lift.Rectangular

open Lattice.Core

variable {m n : ℕ}

/-- **长方阵的满宽编码器**：`W i j` 读 `s[i*n + j]`，`b j` 读 `s[m*n + j]`。 -/
noncomputable def layerOfListRect (s : List ℝ) : LayerParams (Fin m) (Fin n) where
  W := fun i j => s.getD (i.val * n + j.val) 0
  b := fun j => s.getD (m * n + j.val) 0

/-- **读回系数**：位置就是定义里写的那个。 -/
theorem layerOfListRect_W (s : List ℝ) (i : Fin m) (j : Fin n) :
    (layerOfListRect (m := m) (n := n) s).W i j = s.getD (i.val * n + j.val) 0 := rfl

/-- **读回偏置**：在 `m*n` 之后。 -/
theorem layerOfListRect_b (s : List ℝ) (j : Fin n) :
    (layerOfListRect (m := m) (n := n) s).b j = s.getD (m * n + j.val) 0 := rfl

/-- **逆**：系数按除法索引读回，然后偏置。

`Nat.div_lt_iff_lt_mul hn` 把 `k/n < m` 归结为 `0 < n ∧ k < m*n`——后者正是 `k.isLt`。
**不能用 `Nat.div_lt_of_lt_mul`**：它要求除数在前，而 `k` 的类型是 `Fin (m*n)`，重排会破坏 `k.isLt`。 -/
noncomputable def listOfLayerRect (hn : 0 < n) (L : LayerParams (Fin m) (Fin n)) : List ℝ :=
  (List.ofFn (fun k : Fin (m * n) =>
      L.W ⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩ ⟨k.val % n, Nat.mod_lt _ hn⟩)) ++
    (List.ofFn (fun j : Fin n => L.b j))

/-- **逆的长度是 `m*n + n`。** -/
theorem listOfLayerRect_length (hn : 0 < n) (L : LayerParams (Fin m) (Fin n)) :
    (listOfLayerRect hn L).length = m * n + n := by
  unfold listOfLayerRect
  rw [List.length_append, List.length_ofFn, List.length_ofFn]

/-- **往返**：`listOfLayerRect` 是 `layerOfListRect` 的逆（长度匹配时）。

证明结构与方阵版相同：`List.ext_getElem` + `List.getElem_append_left`/`_right`
（它们的下标证明是**隐式**的，所以 `ext` 提供的证明自然匹配），
系数半归约成 `(k/n)*n + k%n = k`，偏置半归约成 `m*n + (k - m*n) = k`。 -/
theorem roundtrip_rect (hn : 0 < n) (s : List ℝ) (hlen : s.length = m * n + n) :
    listOfLayerRect hn (layerOfListRect (m := m) (n := n) s) = s := by
  apply List.ext_getElem
  · rw [listOfLayerRect_length, hlen]
  · intro k h1 h2
    unfold listOfLayerRect
    rcases Nat.lt_or_ge k (m * n) with hk | hk
    · rw [List.getElem_append_left (i := k) (as := List.ofFn (fun k : Fin (m * n) =>
          (layerOfListRect (m := m) (n := n) s).W
            ⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩ ⟨k.val % n, Nat.mod_lt _ hn⟩))
        (by rw [List.length_ofFn]; exact hk)]
      rw [List.getElem_ofFn, layerOfListRect_W]
      rw [Nat.mul_comm (k / n) n, Nat.div_add_mod k n]
      exact List.getD_eq_getElem _ _ h2
    · rw [List.getElem_append_right (i := k) (as := List.ofFn (fun k : Fin (m * n) =>
          (layerOfListRect (m := m) (n := n) s).W
            ⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩ ⟨k.val % n, Nat.mod_lt _ hn⟩))
        (by rw [List.length_ofFn]; exact hk)]
      rw [List.getElem_ofFn, layerOfListRect_b]
      simp only [Fin.val_mk]
      rw [List.length_ofFn, Nat.add_sub_cancel' hk]
      exact List.getD_eq_getElem _ _ h2

/-- **`m = n` 时退化为方阵版**：这是「推广而非平行」的机器检查形式。

方阵版 `layerOfListFull` 的 `W` 与 `b` 与本节的 `layerOfListRect` 在 `m = n` 时逐字相同。 -/
theorem layerOfListRect_eq_full_width {n : ℕ} (s : List ℝ) (i j : Fin n) :
    (layerOfListRect (m := n) (n := n) s).W i j =
        (FullWidth.layerOfListFull (n := n) s).W i j ∧
      (layerOfListRect (m := n) (n := n) s).b j =
        (FullWidth.layerOfListFull (n := n) s).b j :=
  ⟨rfl, rfl⟩

end Lattice.Lift.Rectangular
