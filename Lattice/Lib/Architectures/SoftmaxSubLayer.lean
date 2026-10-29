import Mathlib
import Lattice.Lib.Architectures.RealTransformerEval
import Lattice.Lib.Attention.RealAttention

/-!
# L2-12：把 `softmax` 接成 `RealTransformerEval` 的一个**具体** `SubLayer`

## 量出来的事实：抽象的不是 softmax，是 `SubLayer`

`RealTransformerEval` 的 `SubLayer` 是

    structure SubLayer (n : ℕ) where
      apply : (Fin n → ℝ) → (Fin n → ℝ)

**一个裸函数，没有任何约束**。所以 `Block.eval_lipschitz` 只能**条件地**给出界
（`La`/`Lf`/`Ln` 由调用方提供）——**这不是缺陷，是分层**：Transformer 的结构在那一层，常数在下一层。

**而 `softmax` 早就存在**（`Lib/Attention/RealAttention.lean:87`），且已证明
`softmax_nonneg`、`softmax_sum_one`、`convComb_norm_bound`、`attention_output_bound`。

**所以缺的是那个桥：把 softmax 注意力包成 `SubLayer`。** 本节就是它。

## 本节给出什么、不给出什么

**给出**：
- `softmaxAttention`：由**打分矩阵**与**值矩阵**构成的 `SubLayer`；
- `softmaxAttention_bound`：每个输出坐标被**值的最大绝对值**界住（用 `attention_output_bound`）；
- `softmax_shift`：softmax 的**平移不变性**（树里此前没有）；
- `softmaxBlock`：用具体注意力装配一个 `Block`。

**不给出**：**注意力的 Lipschitz 常数**。`Block.eval_lipschitz` 需要那个数，
而 softmax 的 Lipschitz 界要 `exp` 的均值定理估计——**那是另一件事，本节不做，也不假装。** -/

namespace Lattice.Lib.TransformerEval

open Lattice

/-! ## 一、softmax 的平移不变性 -/

/-- ⭐ **softmax 平移不变**：给所有分数加同一个常数，概率分布不变。

**这是 softmax 数值稳定的原因**，也是它区别于一般 `exp` 归一化的性质。 -/
theorem softmax_shift {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (c : ℝ) :
    softmax (fun j => z j + c) = softmax z := by
  funext i
  unfold softmax
  -- the denominator factors: `∑ j, exp (z j + c) = (∑ j, exp (z j)) * exp c`
  have h1 : (∑ j, Real.exp (z j + c)) = (∑ j, Real.exp (z j)) * Real.exp c := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => Real.exp_add _ _)
  rw [h1, Real.exp_add]
  have hc : Real.exp c ≠ 0 := ne_of_gt (Real.exp_pos c)
  have hd : (∑ j, Real.exp (z j)) ≠ 0 := ne_of_gt (softmax_denom_pos z)
  field_simp
  ring

/-- **`softmax` 每一项严格为正**（`exp` 恒正、分母恒正）。 -/
theorem softmax_pos {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (i : ι) : 0 < softmax z i := by
  unfold softmax
  exact div_pos (Real.exp_pos _) (softmax_denom_pos z)

/-! ## 二、具体注意力：一个 `SubLayer` -/

/-- **softmax 注意力层**：`W` 是打分矩阵，`V` 是值矩阵。

    输出第 `i` 个坐标 = ∑ j, softmax (fun k => W i k * x k) j * V j i

**这是 transformer 注意力的形状**：第 `i` 行给出对 `j` 的权重，输出是值的凸组合。 -/
noncomputable def softmaxAttention {n : ℕ} [NeZero n] (W V : Fin n → Fin n → ℝ) : SubLayer n where
  apply := fun x i => convComb (softmax (fun k => W i k * x k)) (fun j => V j i)

/-- ⭐ **输出被值的最大绝对值界住**：`∀ j, |V j i| ≤ M ⟹ |输出 i| ≤ M`。

**这是 `attention_output_bound` 的直接实例**——softmax 是概率分布，所以凸组合不放大。 -/
theorem softmaxAttention_bound {n : ℕ} [NeZero n] (W V : Fin n → Fin n → ℝ) (M : ℝ) (i : Fin n)
    (hV : ∀ j, |V j i| ≤ M) :
    ∀ x : Fin n → ℝ, |softmaxAttention W V |>.apply x i| ≤ M := by
  intro x
  show |convComb (softmax (fun k => W i k * x k)) (fun j => V j i)| ≤ M
  exact attention_output_bound (fun k => W i k * x k) (fun j => V j i) M hV

/-! ## 三、装配一个具体块 -/

/-- **用具体注意力装配的 `Block`**：注意力是 softmax 的，前馈与归一化仍由调用方给。

**这条让 `RealTransformerEval` 可以被实例化**——此前 `Block.attn` 只能是一个未指定的函数。 -/
noncomputable def softmaxBlock {n : ℕ} [NeZero n] (W V : Fin n → Fin n → ℝ)
    (ff norm : SubLayer n) : Block n where
  attn := softmaxAttention W V
  ff := ff
  norm := norm

/-- **装配后的块，其注意力的 `apply` 就是那个凸组合**（定义相等）。 -/
theorem softmaxBlock_attn {n : ℕ} [NeZero n] (W V : Fin n → Fin n → ℝ) (ff norm : SubLayer n)
    (x : Fin n → ℝ) (i : Fin n) :
    ((softmaxBlock W V ff norm).attn).apply x i
      = convComb (softmax (fun k => W i k * x k)) (fun j => V j i) := rfl

end Lattice.Lib.TransformerEval
