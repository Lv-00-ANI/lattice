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

/-! ## 第二半：对**打分矩阵 `W`** 的 Lipschitz 界

上一节fix住 `W`、让 `x` 动。**这一节反过来**：`x` 不动，`W` 动。

`W` 只影响 softmax 权重 `p j = exp (W i j) / ∑ k, exp (W i k)`，所以

    attention W V x i − attention W' V x i = ∑ j, (p j − p' j) · (V x) j

**而 `|p j − p' j| ≤ 2ε·exp(2ε)`** 由 `SoftmaxLipschitzBound.softmax_lipschitz` 直接给出——
**`p` 就是 `Lattice.softmax (W i)`，所以那条定理不加修改地适用。**

⇒ 剩下的只是 `weighted_average_weights_lipschitz`：**权重扰动、值不动**。

⚠ **这半的常数比 `x` 那半粗糙**：它是 `(2ε·exp(2ε)) · ∑ j, |(V x) j|`，
**对 `j` 求和而非取最大**。紧的会是 `· max_j |(V x) j|`，**但那要 `Finset.sup`。**
`W` 那半的常数还乘上了 softmax 自己的 Lipschitz 常数——**而 `x` 那半不需要它，因为权重不随 `x` 动。** -/

/-- ⭐⭐ **`attention` 对打分矩阵 `W` 的 Lipschitz 界**。

若 `∀ j, |W i j − W' i j| ≤ ε`（只扰动第 `i` 行，因为只有那一行决定查询 `i` 的权重），
则输出的变化不超过 `(2ε·exp(2ε)) · ∑ j, |(V x) j|`。 -/
theorem applyInstr_attention_lipschitz_W {n : ℕ} (hn : 0 < n)
    (W W' V : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (i : Fin n) (h : ∀ j : Fin n, |W i j - W' i j| ≤ ε) :
    |Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W V : _) i
        - Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W' V : _) i|
      ≤ (2 * ε * Real.exp (2 * ε)) * ∑ j, |∑ k, V j k * x k| := by
  haveI := finNonempty hn
  -- the two weight vectors are `softmax (W i)` and `softmax (W' i)`
  have hM : ∀ j : Fin n,
      |Real.exp (W i j) / ∑ k, Real.exp (W i k)
        - Real.exp (W' i j) / ∑ k, Real.exp (W' i k)| ≤ 2 * ε * Real.exp (2 * ε) :=
    fun j => Lattice.Lib.Attention.softmax_lipschitz (W i) (W' i) ε hε h j
  exact weighted_average_weights_lipschitz _ _ _ hM

/-! ## 两半的合成：`x` 与 `W` **同时**扰动

前两节各自固定一个自变量。**这一节让两者同时动**，用三角不等式把两个界加起来：

    attention W V x i − attention W' V x' i
      = (attention W V x i − attention W' V x i)   -- 只动 W，输入是 x
      + (attention W' V x i − attention W' V x' i) -- 只动 x，矩阵是 W'

⚠ **中间点的选择决定了常数的形状。** 取 `attention W' V x i` 意味着
**`W` 那一项用 `x` 的取值**（`∑ j, |(V x) j|`），**`x` 那一项用 `W'`**（常数只含 `V`）。

**另一个选法（中间点 `attention W V x'`）会把 `(V x')` 放进常数。** 两者都对，
**但都无法消掉对输入取值的依赖**——因为 `W` 那半的界本质上依赖 `(V x)` 的大小。
**要消掉它，就得给输入一个界 `B`**，那正是下面 `_bounded` 那条推论做的事。 -/

/-- ⭐⭐ **`attention` 对 `(x, W)` 的联合 Lipschitz 界**。

**两半相加**，常数是 `(2ε·exp(2ε))·∑ j, |(V x) j| + (∑ j, ∑ k, |V j k|)·δ`。

⚠ **它依赖 `x` 的取值**（第一项里的 `∑ j, |(V x) j|`）——**这不是证明的缺陷，是 `W` 那一半的本质**：
权重对 `W` 的敏感度与 `V x` 的大小相乘，而 `V x` 当然依赖 `x`。 -/
theorem applyInstr_attention_lipschitz_joint {n : ℕ} (hn : 0 < n)
    (W W' V : Fin n → Fin n → ℝ) (x x' : Fin n → ℝ) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (i : Fin n) (hx : ∀ k : Fin n, |x k - x' k| ≤ δ)
    (hW : ∀ j : Fin n, |W i j - W' i j| ≤ ε) :
    |Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W V : _) i
        - Lattice.Lift.ProgramAST.applyInstr x' (Lattice.Lift.ProgramAST.Instr.attention W' V : _) i|
      ≤ (2 * ε * Real.exp (2 * ε)) * ∑ j, |∑ k, V j k * x k|
        + (∑ j, ∑ k, |V j k|) * δ := by
  -- split at the point where only `W` has moved
  have hsplit :
      Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W V : _) i
        - Lattice.Lift.ProgramAST.applyInstr x' (Lattice.Lift.ProgramAST.Instr.attention W' V : _) i
      = (Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W V : _) i
          - Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W' V : _) i)
        + (Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W' V : _) i
          - Lattice.Lift.ProgramAST.applyInstr x' (Lattice.Lift.ProgramAST.Instr.attention W' V : _) i) := by
    ring
  rw [hsplit]
  refine le_trans (abs_add _ _) (add_le_add ?_ ?_)
  · exact applyInstr_attention_lipschitz_W hn W W' V x ε hε i hW
  · exact applyInstr_attention_lipschitz hn W' V x x' δ hδ hx i

/-! ## 消掉对输入取值的依赖：给输入一个界 `B`

上一节的界里有 `∑ j, |(V x) j|`——**依赖 `x` 的具体取值**，所以它不是一条"常数"界。
**但若输入被 `B` 逐分量界住，它就可以被 `V` 与 `B` 表出**：

    |(V x) j| ≤ ∑ k, |V j k| · |x k| ≤ B · ∑ k, |V j k|

⇒ `∑ j, |(V x) j| ≤ B · ∑ j, ∑ k, |V j k|`，

**于是整条界只依赖 `V`、`B`、`δ`、`ε`——不依赖任何具体的输入点。**
**那才是通常意义上的 Lipschitz 陈述**，而上一节的是它的"逐点"版本。 -/

/-- ⭐ **行点积的绝对值之和被 `B · (V 的绝对值和)` 界住**（输入逐分量被 `B` 界住时）。

**可推广**：它不提 attention，只谈 `V x` 的范数界——任何"矩阵乘向量"的估计都能用它。 -/
theorem sum_abs_rowDot_le {n : ℕ} (V : Fin n → Fin n → ℝ) (x : Fin n → ℝ) {B : ℝ}
    (hB : ∀ k : Fin n, |x k| ≤ B) (hB0 : 0 ≤ B) :
    ∑ j, |∑ k, V j k * x k| ≤ B * ∑ j, ∑ k, |V j k| := by
  have hrow : ∀ j : Fin n, |∑ k, V j k * x k| ≤ B * ∑ k, |V j k| := by
    intro j
    calc |∑ k, V j k * x k|
        ≤ ∑ k, |V j k * x k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |V j k| * |x k| := Finset.sum_congr rfl (fun k _ => by rw [abs_mul])
      _ ≤ ∑ k, |V j k| * B :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hB k) (abs_nonneg _))
      _ = (∑ k, |V j k|) * B := by rw [Finset.sum_mul]
      _ = B * ∑ k, |V j k| := by rw [mul_comm]
  calc ∑ j, |∑ k, V j k * x k|
      ≤ ∑ j, B * ∑ k, |V j k| := Finset.sum_le_sum (fun j _ => hrow j)
    _ = B * ∑ j, ∑ k, |V j k| := by rw [Finset.mul_sum]

/-- ⭐⭐ **`attention` 的常数型联合 Lipschitz 界**——输入被 `B` 界住时，界不依赖输入点。

这是上一节那条的推论，**但它才是"Lipschitz 常数"这个说法的正式版本**：
右边只含 `V`、`B`、`δ`、`ε`。 -/
theorem applyInstr_attention_lipschitz_joint_bounded {n : ℕ} (hn : 0 < n)
    (W W' V : Fin n → Fin n → ℝ) (x x' : Fin n → ℝ) (ε δ B : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hB0 : 0 ≤ B) (i : Fin n)
    (hx : ∀ k : Fin n, |x k - x' k| ≤ δ) (hB : ∀ k : Fin n, |x k| ≤ B)
    (hW : ∀ j : Fin n, |W i j - W' i j| ≤ ε) :
    |Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.attention W V : _) i
        - Lattice.Lift.ProgramAST.applyInstr x' (Lattice.Lift.ProgramAST.Instr.attention W' V : _) i|
      ≤ (2 * ε * Real.exp (2 * ε)) * (B * ∑ j, ∑ k, |V j k|)
        + (∑ j, ∑ k, |V j k|) * δ := by
  refine le_trans
    (applyInstr_attention_lipschitz_joint hn W W' V x x' ε δ hε hδ i hx hW) ?_
  -- replace the point-dependent mass `∑ j, |(V x) j|` by the uniform bound
  have hle : ∑ j, |∑ k, V j k * x k| ≤ B * ∑ j, ∑ k, |V j k| :=
    sum_abs_rowDot_le V x hB hB0
  have hfac : 0 ≤ 2 * ε * Real.exp (2 * ε) := by positivity
  have hterm : (2 * ε * Real.exp (2 * ε)) * ∑ j, |∑ k, V j k * x k|
      ≤ (2 * ε * Real.exp (2 * ε)) * (B * ∑ j, ∑ k, |V j k|) :=
    mul_le_mul_of_nonneg_left hle hfac
  linarith

end Lattice.Lib.Attention
