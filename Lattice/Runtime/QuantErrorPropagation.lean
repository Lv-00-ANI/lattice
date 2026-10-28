/-
# 逐分量误差如何传播到层的作用

## 0. 补的是哪个缺口

`LayerQuantization.lean` 与 `LayerQuantizationBits.lean` 证的是**逐分量**的界：

```
|dequant (quant L) i j - L i j| ≤ 1       或   < 2^b
```

而两个文件都在边界段里**明确写了**：这个界**不界住层的作用**（`affineAct` 的输出误差）。
本节补上那一块。

## 1. 为什么不能免费得到

`affineAct p x j = (∑ i, p.W i j * x i) + p.b j`。

误差要穿过 `∑ i, W i j * x i`。对**权重**的扰动 `ε` 会被 `∑` 放大 `n` 倍，再乘上
**输入的大小** `|x i|`。所以：

**没有输入的界就没有输出的界**——`affineAct` 对输入线性且无界。

这不是形式化的惰性，是事实：权重差 `ε` 的同一个层，输入 `1` 与输入 `10^6` 的输出差
相差 `10^6` 倍。

## 2. 结论

```lean
theorem affineAct_perturbation
    (hW : ∀ i j, |p.W i j - q.W i j| ≤ ε)
    (hb : ∀ j, |p.b j - q.b j| ≤ ε)
    (hx : ∀ i, |x i| ≤ M) :
    ∀ j, |affineAct p x j - affineAct q x j| ≤ ε * (Fintype.card n) * M + ε
```

三项分别是：**权重的 `n` 倍放大** × **输入界**、加**偏置**的那一份。

证明是标准的三步：`abs_add`（拆和与偏置）→ `Finset.abs_sum_le_sum_abs`（和的绝对 ≤ 绝对的和）
→ `Finset.sum_le_sum` + `mul_le_mul`（逐项放缩）。**没有新想法，只是把已知的不等式串起来。**

## 3. 量化情形的代入

把 `ε = 2^b`（`LayerQuantizationBits` 的界）代入，得到：

**量化层的输出误差 ≤ `2^b * n * M + 2^b`**，其中 `M` 是输入的最大绝对值。

**这个式子的形状是有意义的**：误差随 `n`（宽度）线性增长、随 `M`（激活量级）线性增长。
这解释了为什么大模型对量化更敏感——不是因为位宽，而是因为 `n * M` 变大。

## 4. 与饱和截断的相互作用

`SaturationQuantization.lean` 证明饱和失真是 `max (|x| - B) 0`，**随值无界增长**。
代入本节：若某一分量被截断，则那一项的 `ε` **不是一个常数**，而是 `max (|W| - B) 0`。

所以**带饱和的量化的输出误差也没有常数界**——与逐分量的结论一致，只是经过了 `n * M` 的放大。

## 5. 边界

- **`M` 是必需的假设，不是可以省掉的**：没有它定理是**假的**（取 `x` 任意大即可）。
  这一点写进定理的签名，而不是写在散文里。
- **只对单层陈述**。多层栈（`netAct`）的误差会**复合放大**（每层放大 `n * M` 一次），
  那需要递推，属独立的一节。**本节不声称多层结果。**
- **`n` 用了 `Fintype.card n`**，所以对任意有限指标类型成立，不只是 `Fin n`。
- 本节**不改**任何既有定理。
-/
import Mathlib
import Lattice.Core.Net
import Lattice.Runtime.LayerQuantizationBits

namespace Lattice.Lift.QuantErrorProp

open Lattice.Core

/-- **逐分量界传播到层作用**：权重与偏置的每个分量都差不超过 `ε`，输入每个分量都 ≤ `M`，
则输出的每个分量差不超过 `ε * n * M + ε`。

**三个假设都不多余**：
- `hε`、`hM` 供 `mul_le_mul` 的正性条件；
- `hx` 是**必需的**——没有它定理为假，因为 `affineAct` 对输入线性无界。 -/
theorem affineAct_perturbation {n : Type} [Fintype n]
    (p q : AffineLayer n) (x : n → ℝ) {ε M : ℝ}
    (hε : 0 ≤ ε)
    (hW : ∀ i j, |p.W i j - q.W i j| ≤ ε)
    (hb : ∀ j, |p.b j - q.b j| ≤ ε)
    (hx : ∀ i, |x i| ≤ M) :
    ∀ j, |affineAct p x j - affineAct q x j| ≤ ε * (Fintype.card n : ℝ) * M + ε := by
  intro j
  rw [affineAct, affineAct]
  have hsplit : (∑ i, p.W i j * x i) + p.b j - ((∑ i, q.W i j * x i) + q.b j) =
      (∑ i, (p.W i j - q.W i j) * x i) + (p.b j - q.b j) := by
    have hs : (∑ i, (p.W i j - q.W i j) * x i) =
        (∑ i, p.W i j * x i) - (∑ i, q.W i j * x i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hs]; ring
  rw [hsplit]
  have hbound : |∑ i, (p.W i j - q.W i j) * x i| ≤ ε * (Fintype.card n : ℝ) * M := by
    have step1 : |∑ i, (p.W i j - q.W i j) * x i| ≤
        ∑ i, |p.W i j - q.W i j| * |x i| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact le_of_eq (Finset.sum_congr rfl (fun i _ => by rw [abs_mul]))
    have step2 : (∑ i, |p.W i j - q.W i j| * |x i|) ≤ ∑ _ : n, ε * M := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hW i j) (hx i) (abs_nonneg _) hε
    have step3 : (∑ _ : n, ε * M) = ε * (Fintype.card n : ℝ) * M := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    linarith
  have hb' : |p.b j - q.b j| ≤ ε := hb j
  calc |(∑ i, (p.W i j - q.W i j) * x i) + (p.b j - q.b j)|
      ≤ |∑ i, (p.W i j - q.W i j) * x i| + |p.b j - q.b j| := abs_add _ _
    _ ≤ ε * (Fintype.card n : ℝ) * M + ε := by linarith

/-- **量化层的输出误差**：把 `LayerQuantizationBits` 的逐分量界 `< 2^b` 代入传播引理。

**形状说明**：误差随宽度 `n` 与激活量级 `M` 线性增长，**不由位宽单独决定**。
这解释了大模型对量化更敏感的原因——是 `n * M` 变大，不是 `b` 变小。 -/
theorem quantizedLayer_output_error {n : Type} [Fintype n]
    (p q : AffineLayer n) (x : n → ℝ) (b : ℕ) {M : ℝ}
    (hW : ∀ i j, |p.W i j - q.W i j| < (2 : ℝ) ^ b)
    (hb : ∀ j, |p.b j - q.b j| < (2 : ℝ) ^ b)
    (hx : ∀ i, |x i| ≤ M) :
    ∀ j, |affineAct p x j - affineAct q x j| ≤
      (2 : ℝ) ^ b * (Fintype.card n : ℝ) * M + (2 : ℝ) ^ b := by
  have hε : (0 : ℝ) ≤ 2 ^ b := by positivity
  exact affineAct_perturbation p q x hε
    (fun i j => le_of_lt (hW i j)) (fun j => le_of_lt (hb j)) hx

end Lattice.Lift.QuantErrorProp
