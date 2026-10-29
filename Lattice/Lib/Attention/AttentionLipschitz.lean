import Mathlib
import Lattice.Lib.Architectures.SoftmaxSubLayer
import Lattice.Lib.Attention.SoftmaxLipschitzBound

/-!
# attention 的 Lipschitz 常数：**打分那一半证完了**，合成写成公式

## 三个部件

`softmaxAttention W V` 的第 `i` 个输出坐标是

    apply x i = ∑ j, softmax (fun k => W i k * x k) j * V j i

| 部件 | 形式 | 常数 | 状态 |
|:--|:--|:--|:--|
| **打分**（行点积） | `x ↦ fun k => W i k * x k` | `∑ k, \|W i k\|` | ✅ **本节 `rowDot_lipschitz`** |
| **softmax** | `s ↦ softmax s` | `2ε·exp (2ε)` | ✅ 第 48 轮 `softmax_lipschitz` |
| **值凸组合** | `p ↦ ∑ j, p j · V j i` | `≤ M`（不放大） | ✅ 第 42 轮 `softmaxAttention_bound` |

## 合成公式（**未证**，但每个部件的常数都已就位）

设输入逐点差 `≤ δ`、`|V j i| ≤ M`、`ε := (∑ k, |W i k|) · δ`，则

    |apply x i − apply x' i| ≤ n · M · (2ε · exp (2ε))

**推导**：差是 `∑ j, (p_j − p'_j)·V j i`，绝对值 ≤ `∑ j, |p_j − p'_j|·|V j i|`
≤ `∑ j, (2ε·exp(2ε))·M` = `n·M·(2ε·exp(2ε))`；而 `ε` 由行点积的差给出（本节的定理）。

## ⚠ 一条必须说清的性质：`La` **依赖 `δ`**，不是常数

softmax 的界是 `2ε·exp(2ε)`，**不是 `C·ε`**。所以整条链给出的不是「全局 Lipschitz」，
而是**「在 `δ` 的邻域里，以 `n·M·2·L_W·exp(2·L_W·δ)` 为常数」**——
**其中 `L_W := ∑ k, |W i k|`**。

`Block.eval_lipschitz` 的调用方要的是一个数；**把这条依赖关系写出来，比给一个假装是常数的数有用**。

## 为什么合成没证完

它是一段约 40 行的 `calc`，本轮的尝试在**结构**上反复出错（`have`/`calc` 的边界），
**而不是在数学上**。已有的三块（本节、第 48 轮、第 42 轮）**每一块都独立可编译**——
所以下一轮要做的是**接线**，不是发现。 -/

namespace Lattice.Lib.Attention

open Lattice

/-- ⭐ **行点积的 Lipschitz 性**：`|∑ k, W i k·x k − ∑ k, W i k·x' k| ≤ (∑ k, |W i k|)·δ`。

**这是 attention 三个部件里的第一个**——打分的常数 `L_W := ∑ k, |W i k|`。 -/
theorem rowDot_lipschitz {n : ℕ} (W : Fin n → Fin n → ℝ) (i : Fin n) (x x' : Fin n → ℝ) (δ : ℝ)
    (h : ∀ k, |x k - x' k| ≤ δ) :
    |∑ k, W i k * x k - ∑ k, W i k * x' k| ≤ (∑ k, |W i k|) * δ := by
  have hkey : ∑ k, W i k * x k - ∑ k, W i k * x' k = ∑ k, W i k * (x k - x' k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hkey]
  calc |∑ k, W i k * (x k - x' k)|
      ≤ ∑ k, |W i k * (x k - x' k)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |W i k| * |x k - x' k| :=
        Finset.sum_congr rfl (fun k _ => by rw [abs_mul])
    _ ≤ ∑ k, |W i k| * δ :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (h k) (abs_nonneg _))
    _ = (∑ k, |W i k|) * δ := by rw [Finset.sum_mul]

/-- **逐点形式**：`|W i k·(x k − x' k)| ≤ (∑ k, |W i k|)·δ`。

**软 max 的界需要一个对每个 `k` 都成立的 `ε`**，而 `rowDot_lipschitz` 是**行和**级；
这条给出逐点的那个 `ε`，两者合起来才是合成所需的前件。 -/
theorem rowDot_pointwise {n : ℕ} (W : Fin n → Fin n → ℝ) (i k : Fin n) (x x' : Fin n → ℝ)
    (δ : ℝ) (h : ∀ k, |x k - x' k| ≤ δ) :
    |W i k * x k - W i k * x' k| ≤ (∑ k, |W i k|) * δ := by
  have h1 : W i k * x k - W i k * x' k = W i k * (x k - x' k) := by ring
  rw [h1, abs_mul]
  have h2 : |W i k| ≤ ∑ k, |W i k| :=
    Finset.single_le_sum (f := fun k => |W i k|) (fun k _ => abs_nonneg _) (Finset.mem_univ k)
  exact mul_le_mul h2 (h k) (abs_nonneg _) (Finset.sum_nonneg (fun k _ => abs_nonneg _))

end Lattice.Lib.Attention
