import Mathlib
import Lattice.Core.Net

/-!
# `CInterface/Serialization` —— **词级**序列化契约（不是字节级）

## 为什么是「词」而不是「字节」

`DIRECTORY-DESIGN.md` §8.1 要「token/weight/profile 的字节格式」。实测：token 是 `List Int`、
权重是 `AffineLayer (Fin k)`（`W : Fin k → Fin k → ℝ`、`b : Fin k → ℝ`），而 **`profile` 不存在**
（第 15 轮：23 个具名类型里 17 个没有）。**字节**这一步卡在 `ℝ` 上：Lean 里 `ℝ` 是抽象的，
没有可计算的字节表示，接 IEEE-754 需要舍入模型（`Lib/Quantization/RealIEEE754` 里有，但那是另一条链）。

## 本文件证明了什么

| 定理 | 内容 |
|:--|:--|
| `layerWords_length` | **参数数恰好 `k * k + k`**——布局总长度，C 侧缓冲大小由它决定 |
| `wPart_length` | `W` 段长度是 `k*k` |
| `idxW_lt` / `idxB_lt` | 两个索引在界内的算术 |
| **`layerWords_getD_W`** | **第 `i*k+j` 个词就是 `W i j`**（行主序可逆的**权重那一半**） |

## ⚠ 本文件**没有**证明什么（已登记）

- **`b` 那一半的取回未证。** 目标形状是
  `(layerWords L).getD (k*k + j.val) 0 = L.b j`。第 25 轮试到第 10 次仍未过：
  `List.getElem_append_right` 的 `i - as.length` 让目标落在 `Fin.cast` 的**依赖位置**上，
  `rw [hWlen]` 报 *motive is not type correct*；
  改走 `List.getD_append_right`（普通 `Nat` 索引）是对的方向，但
  `unfold layerWords` 之后目标里的 `map` 已被化简，`getD_eq_getElem` 的默认值/列表形状与我预期的不一致。
  **下一步的确切起点**：`set` 住 `wl := (finRange (k*k)).map …` 与 `bl := (finRange k).map (fun j => L.b j)`
  再做 `getD_append_right`，让两侧都不被 `unfold` 化简。
- **`layerWords_injective`** 依赖上面那一半，故也未证。
- **字节级**（字节序、对齐、填充、`ℝ` 的二进制表示）未做；**`Conformance`** 的 `Float` 模型见该文件。

**`sorry` 不可接受，所以缺的那一半留空，并把两次尝试的确切障碍写在这里。** -/

namespace Lattice.CInterface.Serialization

open Lattice.Core

/-- **一层的词序列**：`k*k` 个权重（行主序，索引 `i*k+j` 处是 `W i j`），再接 `k` 个偏置。 -/
noncomputable def layerWords {k : ℕ} (L : AffineLayer (Fin k)) : List ℝ :=
  (List.finRange (k * k)).map (fun idx => L.W (Fin.divNat idx) (Fin.modNat idx)) ++
    (List.finRange k).map (fun j => L.b j)

/-- **解码器**：把词序列读回一层。用 `getD`，不需要索引在界内的证明。 -/
noncomputable def wordsLayer {k : ℕ} (w : List ℝ) : AffineLayer (Fin k) where
  W i j := w.getD (i.val * k + j.val) 0
  b j := w.getD (k * k + j.val) 0

/-- ⭐ **参数数公式**：`k` 宽的仿射层恰好 `k * k + k` 个词。

**这是布局的总长度**，不是估计——C 侧的缓冲大小由它决定。 -/
theorem layerWords_length {k : ℕ} (L : AffineLayer (Fin k)) :
    (layerWords L).length = k * k + k := by
  unfold layerWords
  rw [List.length_append, List.length_map, List.length_map, List.length_finRange,
      List.length_finRange]

/-- `W` 段的长度是 `k*k`。 -/
theorem wPart_length {k : ℕ} (L : AffineLayer (Fin k)) :
    ((List.finRange (k * k)).map
      (fun idx => L.W (Fin.divNat idx) (Fin.modNat idx))).length = k * k := by
  rw [List.length_map, List.length_finRange]

/-- `i*k + j < k*k`。`i.isLt` 同时给出 `k > 0`。 -/
theorem idxW_lt {k : ℕ} (i j : Fin k) : i.val * k + j.val < k * k := by
  have hi : i.val + 1 ≤ k := by have := i.isLt; omega
  have hj : j.val < k := j.isLt
  calc i.val * k + j.val < i.val * k + k := by omega
    _ = (i.val + 1) * k := by ring
    _ ≤ k * k := Nat.mul_le_mul_right k hi

/-- `k*k + j < k*k + k`。 -/
theorem idxB_lt {k : ℕ} (j : Fin k) : k * k + j.val < k * k + k := by
  have hj : j.val < k := j.isLt
  omega

/-- ⭐ **行主序的可逆性（权重那一半）**：第 `i*k+j` 个词就是 `W i j`。

这条把「摊平」变成**可逆**的——`Fin.divNat`/`Fin.modNat` 把 `Fin (k*k)` 拆回 `(i, j)`，
两个除法引理再确认它们正是 `i` 与 `j`。 -/
theorem layerWords_getD_W {k : ℕ} (L : AffineLayer (Fin k)) (i j : Fin k) :
    (layerWords L).getD (i.val * k + j.val) 0 = L.W i j := by
  have hjk : j.val < k := j.isLt
  have hidx : i.val * k + j.val < (layerWords L).length := by
    rw [layerWords_length]
    exact Nat.lt_trans (idxW_lt i j) (by omega)
  rw [List.getD_eq_getElem _ _ hidx]
  have hWlen := wPart_length L
  unfold layerWords
  rw [List.getElem_append_left (h := by rw [hWlen]; exact idxW_lt i j),
      List.getElem_map, List.getElem_finRange]
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) hjk
  have hdiv : (i.val * k + j.val) / k = i.val := by
    rw [Nat.mul_comm i.val k, Nat.mul_add_div hk, Nat.div_eq_of_lt hjk, Nat.add_zero]
  have hmod : (i.val * k + j.val) % k = j.val := by
    rw [Nat.mul_comm i.val k, Nat.mul_add_mod, Nat.mod_eq_of_lt hjk]
  congr 1
  · apply Fin.ext
    show (i.val * k + j.val) / k = i.val
    exact hdiv
  · apply Fin.ext
    show (i.val * k + j.val) % k = j.val
    exact hmod

/-- **退化情形**：`k = 0` 时词序列为空，与 `k * k + k = 0` 一致。 -/
theorem layerWords_zero (L : AffineLayer (Fin 0)) : layerWords L = [] := by
  unfold layerWords
  simp

end Lattice.CInterface.Serialization
