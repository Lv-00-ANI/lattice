/-
# 块级蒸馏的 `Ls`：**由权重导出**，而不是当作自由参数

## 为什么需要这个文件

`Lib/LearningTheory/RealDistill.chain_distill_bound_lipschitz` 的陈述里，
`Ls : ℕ → ℝ` 是**自由函数**，前提 `hLt`/`hLs` 只说「每层是 `Ls i`-Lipschitz」。
doc 自己写着「**诚实假设**：师生层共享常数上界 `Ls i`（若不同取 max）」——
也就是说 **`Ls` 从未由权重导出**。

`PROOF-DEBT` 的 `register` 条目记的正是这件事：真正缺的是**把逐层常数 `Ls` 从网络结构导出的桥**。

## 桥在哪，以及它其实已经有一半

实测（第 21 轮，见 `DISTILL-LS-MEASUREMENT.md`）：**零件已经存在**，只是形式不匹配。

| 已有 | 位置 | 形式 |
|:--|:--|:--|
| `affineAct_lipschitz` | `Runtime/StackError.lean:120` | **逐分量** |
| `layerMag_nonneg` | 同上 `:106` | `0 ≤ layerMag L` |

**缺的是两步**：逐分量 → sup 范数；师生取 max。第 2 步是物流，第 1 步是唯一的卡点——
而它的正确写法是 **`rw [pi_norm_le_iff_of_nonneg h]` 然后 `intro`**
（mathlib 自己的用法；`|>.mpr` 无法推断隐含的 `f`）。

## 边界

- **只做仿射层**：它**恰好**有 `layerMag` 这个**可计算的上界**。
  **不声称 `layerMag` 是算子范数的最优值**——定理里说的是 `≤`。
- **非线性层（激活、注意力）各自的常数**在 `Lib/Architectures/RealBlockLipschitz` 一带，
  **本节不声称已接上**。 -/
import Mathlib
import Lattice.Core.Net
import Lattice.Runtime.StackError
import Lattice.Lib.LearningTheory.RealDistill

namespace Lattice.Lib.DistillLip

open Lattice.Core
open Lattice.Lift.StackError
open scoped BigOperators

/-- ⭐ **`affineAct` 的 Lipschitz 性（`‖·‖` 形式）**：把 `StackError.affineAct_lipschitz` 的
**逐分量**形式提升到 `Fin n → ℝ` 的 sup 范数。

偏差 `b` 在差分中抵消，所以常数只来自 `W`。 -/
theorem affineAct_lipschitz_norm {n : ℕ} (L : AffineLayer (Fin n)) (u v : Fin n → ℝ) :
    ‖affineAct L u - affineAct L v‖ ≤ layerMag L * ‖u - v‖ := by
  have hδ : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hcoord : ∀ i, |u i - v i| ≤ ‖u - v‖ := by
    intro i
    have := norm_le_pi_norm (u - v) i
    simpa [Pi.sub_apply] using this
  have hbound := Lattice.Lift.StackError.affineAct_lipschitz L u v hδ hcoord
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (layerMag_nonneg L) hδ)]
  intro j
  have h := hbound j
  simpa [Pi.sub_apply, Real.norm_eq_abs] using h

/-- ⭐⭐ **块级蒸馏的 `Ls` 由权重导出**：`Ls i := max (layerMag (Wt i)) (layerMag (Ws i))`。

这是 `chain_distill_bound_lipschitz` 的**实例化**——但 `Ls` 不再是自由参数，
而是**由两侧权重算出来的**（师生不同所以取 `max`，正是原 doc 说「若不同取 max」的那一步）。

**所以「逐层常数是自由参数」这个缺口，对仿射层闭合了。** -/
theorem chain_distill_affine {n : ℕ} (Wt Ws : ℕ → AffineLayer (Fin n)) (ε : ℕ → ℝ) (m : ℕ)
    (hε : ∀ i, i < m → ∀ y, ‖affineAct (Wt i) y - affineAct (Ws i) y‖ ≤ ε i) :
    ∀ x : Fin n → ℝ,
      ‖ChainFwd (fun i => affineAct (Wt i)) m x - ChainFwd (fun i => affineAct (Ws i)) m x‖
        ≤ ∑ i in Finset.range m,
            (∏ j in Finset.Ioo i m, max (layerMag (Wt j)) (layerMag (Ws j))) * ε i := by
  set Ls : ℕ → ℝ := fun i => max (layerMag (Wt i)) (layerMag (Ws i)) with hLs
  have hL0 : ∀ i, i < m → 0 ≤ Ls i := by
    intro i _
    exact le_trans (layerMag_nonneg (Wt i)) (le_max_left _ _)
  have hLt : ∀ i, i < m → ∀ x y : Fin n → ℝ,
      ‖affineAct (Wt i) x - affineAct (Wt i) y‖ ≤ Ls i * ‖x - y‖ := by
    intro i _ x y
    calc ‖affineAct (Wt i) x - affineAct (Wt i) y‖
        ≤ layerMag (Wt i) * ‖x - y‖ := affineAct_lipschitz_norm (Wt i) x y
      _ ≤ Ls i * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hLs' : ∀ i, i < m → ∀ x y : Fin n → ℝ,
      ‖affineAct (Ws i) x - affineAct (Ws i) y‖ ≤ Ls i * ‖x - y‖ := by
    intro i _ x y
    calc ‖affineAct (Ws i) x - affineAct (Ws i) y‖
        ≤ layerMag (Ws i) * ‖x - y‖ := affineAct_lipschitz_norm (Ws i) x y
      _ ≤ Ls i * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  exact Lattice.chain_distill_bound_lipschitz
    (fun i => affineAct (Wt i)) (fun i => affineAct (Ws i)) Ls ε m hLt hLs' hL0 hε

end Lattice.Lib.DistillLip
