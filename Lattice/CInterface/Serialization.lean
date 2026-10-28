/-
# `CInterface/Serialization` —— **词级**序列化契约（不是字节级）

## 为什么是「词」而不是「字节」

`DIRECTORY-DESIGN.md` §8.1 要「token/weight/profile 的字节格式」。实测：

- **`token` 与 `weight` 的载体存在**：token 是 `List Int`，权重是 `AffineLayer (Fin k)`
  （`W : Fin k → Fin k → ℝ`、`b : Fin k → ℝ`）；
- **`profile` 不存在**（第 15 轮：23 个具名类型里 17 个没有）。

而**字节**这一步卡在 `ℝ` 上：`ℝ` 在 Lean 里是抽象的，**没有可计算的字节表示**。
把它接到 IEEE-754 需要一个**模型**（`Lib/Quantization/RealIEEE754` 里有），
但那是**另一条**证明链，且需要 `ℝ → Float` 的舍入约定。**所以本文件不写字节。**

## 本文件证明了什么

| 定理 | 它在说什么 |
|:--|:--|
| `layerWords_length` | **参数数恰好 `k * k + k`**——布局的总长度，C 侧缓冲大小由它决定 |
| `layerWords_nil` | `k = 0` 时是空表（退化情形，与 `k*k+k = 0` 一致） |

## 本文件**没有**证明什么（已登记的缺口）

⚠ **`layerWords` 的单射性未证。** 那是格式契约的另一半——「词序列相同 ⟹ 层相同」。

**为什么没做**：它需要两条**取回引理**（第 `i*k+j` 个词是 `W i j`，第 `k*k+j` 个是 `b j`），
而这两条要穿过 `List.flatten` / `List.map` 的 `getElem` 管道。第 17 轮试过一次，
`List.getElem_flatten` 的索引形式与 `omega` 的算术目标没对上，**没有写成**。
**`sorry` 不可接受，所以宁可不写这一半，也不写一条假的。**

⭐ **这半条缺口是可执行的**：取回引理是纯 `List` 引理，不涉及任何数学；
把它补上就能得到 `layerWords_injective`，进而得到「格式无损」。 -/
import Mathlib
import Lattice.Core.Net

namespace Lattice.CInterface.Serialization

open Lattice.Core

/-- **一层的词序列**：`W` 行主序摊平，再接上 `b`。

长度是 `k * k + k`，见 `layerWords_length`。 -/
noncomputable def layerWords {k : ℕ} (L : AffineLayer (Fin k)) : List ℝ :=
  ((List.finRange k).map (fun i => (List.finRange k).map (fun j => L.W i j))).flatten ++
    (List.finRange k).map (fun j => L.b j)

/-- ⭐ **参数数公式**：`k` 宽的仿射层恰好 `k * k + k` 个词。

**这是布局的总长度**，不是估计——C 侧的缓冲大小由它决定。 -/
theorem layerWords_length {k : ℕ} (L : AffineLayer (Fin k)) :
    (layerWords L).length = k * k + k := by
  unfold layerWords
  rw [List.length_append]
  have hW : ((List.finRange k).map (fun i => (List.finRange k).map (fun j => L.W i j))).flatten.length
      = k * k := by
    rw [List.length_flatten]
    -- prove the row-length map by induction: it is `replicate (number of rows) k`
    have hc : ∀ l : List (Fin k),
        List.map List.length (List.map (fun i => (List.finRange k).map (fun j => L.W i j)) l)
          = List.replicate l.length k := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih => simp [ih, List.replicate_succ]
    rw [hc, List.length_finRange, List.sum_replicate, smul_eq_mul]
  have hb : ((List.finRange k).map (fun j => L.b j)).length = k := by simp
  rw [hW, hb]
/-- **退化情形**：`k = 0` 时词序列为空，与 `k * k + k = 0` 一致。 -/
theorem layerWords_zero (L : AffineLayer (Fin 0)) : layerWords L = [] := by
  unfold layerWords
  simp

end Lattice.CInterface.Serialization
