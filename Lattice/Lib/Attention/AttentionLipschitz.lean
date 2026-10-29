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

## ✅ 合成（第 50 轮证完）

设输入逐点差 `≤ δ`、`|V j i| ≤ M`、`ε := (∑ k, |W i k|) · δ`，则

    |apply x i − apply x' i| ≤ n · M · (2ε · exp (2ε))

见 `softmaxAttention_lipschitz`。**推导**：差是 `∑ j, (p_j − p'_j)·V j i`，
绝对值 ≤ `∑ j, |p_j − p'_j|·|V j i|` ≤ `∑ j, (2ε·exp(2ε))·M` = `n·M·(2ε·exp(2ε))`。

**证明里没有用 `calc`**：四步各写成一条 `have`，用 `le_trans` 串起来。
第 49 轮的失败全部来自把 `calc` 与 `have` 混在同一段里——**结构问题用结构手段解决**。

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

variable {n : ℕ}

/-- ⭐⭐⭐ **attention 输出的 Lipschitz 界**。

输入逐点差 `≤ δ`、值有界 `|V j i| ≤ M`，则

    |apply x i − apply x' i| ≤ n · M · (2·L_W·δ · exp (2·L_W·δ)),      L_W := ∑ k, |W i k|

**三个部件在这里合成**：打分（`rowDot_pointwise`，常数 `L_W`）、
softmax（`softmax_lipschitz`，常数 `2ε·exp(2ε)`）、值凸组合（不放大，`≤ M`）。

⚠ **`La` 依赖 `δ`**：softmax 的界是 `2ε·exp(2ε)` 而不是 `C·ε`，所以这不是全局 Lipschitz 常数。 -/
theorem softmaxAttention_lipschitz [NeZero n] (W V : Fin n → Fin n → ℝ) (i : Fin n)
    (x x' : Fin n → ℝ) (δ M : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ k, |x k - x' k| ≤ δ) (hV : ∀ j, |V j i| ≤ M) :
    |(Lattice.Lib.TransformerEval.softmaxAttention W V).apply x i
        - (Lattice.Lib.TransformerEval.softmaxAttention W V).apply x' i|
      ≤ (n : ℝ) * M * (2 * ((∑ k, |W i k|) * δ) * Real.exp (2 * ((∑ k, |W i k|) * δ))) := by
  -- 1. the scoring constant is non-negative
  have hLW : 0 ≤ ∑ k, |W i k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hεpos : 0 ≤ (∑ k, |W i k|) * δ := mul_nonneg hLW hδ
  -- 2. the scoring difference, pointwise
  have hscore : ∀ k, |W i k * x k - W i k * x' k| ≤ (∑ k, |W i k|) * δ :=
    fun k => rowDot_pointwise W i k x x' δ h
  -- 3. softmax is Lipschitz at that epsilon
  have hlip : ∀ j, |softmax (fun k => W i k * x k) j - softmax (fun k => W i k * x' k) j|
      ≤ 2 * ((∑ k, |W i k|) * δ) * Real.exp (2 * ((∑ k, |W i k|) * δ)) :=
    fun j => softmax_lipschitz _ _ _ hεpos hscore j
  -- 4. the difference is the sum of the pointwise differences
  have hkey : (Lattice.Lib.TransformerEval.softmaxAttention W V).apply x i
        - (Lattice.Lib.TransformerEval.softmaxAttention W V).apply x' i
      = ∑ j, (softmax (fun k => W i k * x k) j - softmax (fun k => W i k * x' k) j) * V j i := by
    simp only [Lattice.Lib.TransformerEval.softmaxAttention, convComb, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- 5. four inequalities, chained by `le_trans`
  have h1 : |(Lattice.Lib.TransformerEval.softmaxAttention W V).apply x i
          - (Lattice.Lib.TransformerEval.softmaxAttention W V).apply x' i|
      ≤ ∑ j, |(softmax (fun k => W i k * x k) j - softmax (fun k => W i k * x' k) j) * V j i| := by
    rw [hkey]
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ j, |(softmax (fun k => W i k * x k) j - softmax (fun k => W i k * x' k) j) * V j i|
      = ∑ j, |softmax (fun k => W i k * x k) j - softmax (fun k => W i k * x' k) j| * |V j i| :=
    Finset.sum_congr rfl (fun j _ => by rw [abs_mul])
  have h3 : ∑ j, |softmax (fun k => W i k * x k) j - softmax (fun k => W i k * x' k) j| * |V j i|
      ≤ ∑ _j : Fin n, (2 * ((∑ k, |W i k|) * δ) * Real.exp (2 * ((∑ k, |W i k|) * δ))) * M :=
    Finset.sum_le_sum (fun j _ =>
      mul_le_mul (hlip j) (hV j) (abs_nonneg _) (by positivity))
  have h4 : (∑ _j : Fin n, (2 * ((∑ k, |W i k|) * δ) * Real.exp (2 * ((∑ k, |W i k|) * δ))) * M)
      = (n : ℝ) * M * (2 * ((∑ k, |W i k|) * δ) * Real.exp (2 * ((∑ k, |W i k|) * δ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  refine le_trans h1 ?_
  rw [h2]
  refine le_trans h3 ?_
  rw [h4]

end Lattice.Lib.Attention
