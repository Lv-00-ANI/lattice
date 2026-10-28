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
| `idxW_lt` / `idxB_lt` | 两个下标在界内的算术 |
| **`layerWords_getD_W`** | **第 `i*k+j` 个词就是 `W i j`** |
| **`bl_getD`** | 偏置段的第 `j` 个词就是 `b j` |
| **`layerWords_getD_b`** | **第 `k*k+j` 个词就是 `b j`** |
| **`wordsLayer_layerWords`** | **解码器是编码器的左逆**（L0-2） |
| **`layerWords_injective`** | **无损**：词序列相同 ⟹ 层相同（L0-1） |

**`getD_W` 与 `getD_b` 合起来**就是格式契约的另一半：**摊平是可逆的**。

## 本文件**没有**做的事

⚠ **字节级**（字节序、对齐、填充、`ℝ` 的二进制表示）**未做**——原因见上。
**`CInterface/Layout`** 需要 `Model`/`Profile`/`Program`/`Certificate` 的布局，而其中**三个在活树里
不存在**（第 15 轮实测），所以那一块**被测量挡住**，不是被难度挡住。 -/
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

`Fin.divNat`/`Fin.modNat` 把 `Fin (k*k)` 拆回 `(i, j)`，两个除法引理再确认它们正是 `i` 与 `j`。 -/
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

/-- ⭐ **偏置段的取回**：`(finRange k).map (fun j => L.b j)` 的第 `j` 个词就是 `b j`。

**单独成条**，因为它的元素类型是 `ℝ`（而不是 `Fin k`）——这正是第 25 轮把
`getD_eq_getElem` 的默认值搞错的地方。把这一条与 `getD_append_right` 的整段下标算术分开，
两边都不必穿过 `Fin.cast` 的依赖位置。 -/
theorem bl_getD {k : ℕ} (L : AffineLayer (Fin k)) (j : Fin k) :
    ((List.finRange k).map (fun j => L.b j)).getD j.val 0 = L.b j := by
  have hidx : j.val < ((List.finRange k).map (fun j => L.b j)).length := by
    rw [List.length_map, List.length_finRange]
    exact j.isLt
  rw [List.getD_eq_getElem _ _ hidx]
  rw [List.getElem_map, List.getElem_finRange]
  -- `congr 1` closes it: the `Fin` produced by `getElem_finRange` is definitionally `j`
  congr 1

/-- ⭐ **行主序的可逆性（偏置那一半）**：第 `k*k+j` 个词就是 `b j`。

走 `List.getD_append_right`（**普通 `Nat` 下标**），再交给 `bl_getD`——
所以这一段不需要在 `Fin.cast` 的依赖位置上重写。 -/
theorem layerWords_getD_b {k : ℕ} (L : AffineLayer (Fin k)) (j : Fin k) :
    (layerWords L).getD (k * k + j.val) 0 = L.b j := by
  have hWlen := wPart_length L
  unfold layerWords
  rw [List.getD_append_right _ _ _ _ (by rw [hWlen]; exact Nat.le_add_right _ _)]
  rw [hWlen, Nat.add_sub_cancel_left]
  exact bl_getD L j

/-- ⭐⭐ **L0-2：解码器是编码器的左逆。** -/
theorem wordsLayer_layerWords {k : ℕ} (L : AffineLayer (Fin k)) :
    wordsLayer (layerWords L) = L := by
  cases L with
  | mk W b =>
    simp only [wordsLayer, layerWords_getD_W, layerWords_getD_b]

/-- ⭐⭐ **L0-1：无损**——词序列相同 ⟹ 层相同。

**证明走解码器，不走依赖重写**：`congrArg` 作用在**列表**相等上，得到的两个等式都是**层**等式，
再用左逆消掉编码器。（第 18 轮直接 `rw [h] at h₁` 会报 *motive is not type correct*，
因为那条等式的索引依赖 `L`；`congrArg` 之后就没有依赖索引了。） -/
theorem layerWords_injective {k : ℕ} : Function.Injective (layerWords (k := k)) := by
  intro L₁ L₂ h
  have h' := congrArg (wordsLayer (k := k)) h
  rwa [wordsLayer_layerWords, wordsLayer_layerWords] at h'

/-- **退化情形**：`k = 0` 时词序列为空，与 `k * k + k = 0` 一致。 -/
theorem layerWords_zero (L : AffineLayer (Fin 0)) : layerWords L = [] := by
  unfold layerWords
  simp

end Lattice.CInterface.Serialization
