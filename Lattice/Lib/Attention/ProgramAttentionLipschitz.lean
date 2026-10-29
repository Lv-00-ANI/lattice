import Mathlib
import Lattice.Lib.Attention.AttentionLipschitz
import Lattice.Lib.Attention.ConvexCombination
import Lattice.Lib.Attention.ProgramSoftmaxBridge
import Lattice.Runtime.ProgramAST

/-!
# `Lattice.Lib.Attention.ProgramAttentionLipschitz` — **AST 的 `attention` 对输入 `x` 的 Lipschitz 界**

## 为什么这条比 softmax 的 Lipschitz **简单得多**

`Lib/Attention/AttentionLipschitz.lean` 里已有 `softmaxAttention_lipschitz`，它的证明要过 softmax 的
Lipschitz（因为那里的打分**随 `x` 变**）。**而在本 AST 的定义里，权重根本不随 `x` 动**：

```lean
| .attention W V => fun i => ∑ j, (exp (W i j) / ∑ k, exp (W i k)) * (∑ k, V j k * x k)
```

`exp (W i j) / ∑ k, exp (W i k)` **只依赖 `W` 与 `i`，不依赖 `x`**。所以

    attention x i − attention x' i = ∑ j, p j * ((V x) j − (V x') j)

**这是一个加权平均的差，权重非负、和为 1。** ⇒ **`weighted_average_lipschitz` 直接给出结论**，
**而 `V x` 那一侧的差由 `rowDot_lipschitz` 提供。**

⚠ **所以这里的界比常见文献的「attention 是 Lipschitz」更强也更弱**：
**更强**是因为它不需要 softmax 的 Lipschitz 常数（权重不随输入动）；
**更弱**是因为它只对 `x` 成立，不对 `W`/`V` 成立（换权重当然会换输出）。
**本文件只声称前者。**

## 常数

`(∑ j, ∑ k, |V j k|) * δ`。**这是对 `j` 的求和，不是最大值**——技术上更糙
（真正紧的是 `max_j ∑ k |V j k|`），**但它避免引入 `Finset.sup`**，
而**求和形式仍然是一条正确的界**。紧常数留给后续。
-/

namespace Lattice.Lib.Attention

/-- ⭐⭐ **`attention` 对输入 `x` 的 Lipschitz 界**。

若 `∀ k, |x k − x' k| ≤ δ`，则 `|attention x i − attention x' i| ≤ (∑ j, ∑ k, |V j k|) · δ`。

**对任意查询行 `i` 成立，且与 `W` 无关**——因为 `W` 只决定权重，而权重不随 `x` 变。 -/
theorem applyInstr_attention_lipschitz {n : ℕ} (hn : 0 < n) (W V : Fin n → Fin n → ℝ)
    (x x' : Fin n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ k : Fin n, |x k - x' k| ≤ δ)
    (i : Fin n) :
    |Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W V : _) i
        - Lattice.Lift.ProgramAST.applyInstr x' (Lattice.Lift.ProgramAST.Instr.attention W V : _) i|
      ≤ (∑ j, ∑ k, |V j k|) * δ := by
  haveI := finNonempty hn
  -- the weights do not depend on `x`, so both sides share them
  have hp0 : ∀ j : Fin n, 0 ≤ Real.exp (W i j) / ∑ k, Real.exp (W i k) := fun j =>
    div_nonneg (Real.exp_pos _).le (sum_exp_pos (W i)).le
  have hp1 : ∑ j : Fin n, Real.exp (W i j) / ∑ k, Real.exp (W i k) = 1 :=
    Lattice.softmax_sum_one (W i)
  -- each value component is `rowDot_lipschitz`, bounded by the total mass times `δ`
  have hrow : ∀ j : Fin n,
      |(∑ k, V j k * x k) - (∑ k, V j k * x' k)| ≤ (∑ j, ∑ k, |V j k|) * δ := by
    intro j
    refine le_trans (rowDot_lipschitz V j x x' δ h) ?_
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun a => ∑ k, |V a k|) (fun a _ => Finset.sum_nonneg (fun k _ => abs_nonneg _))
        (Finset.mem_univ j)) hδ
  exact weighted_average_lipschitz _ _ _ hp0 hp1 hrow

end Lattice.Lib.Attention
