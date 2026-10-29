import Mathlib

/-!
# `Lattice.Lib.Attention.ConvexCombination` — **加权平均落在极值之间**

## 为什么单独一个文件

这条引理**不提 softmax、不提 attention、不提任何本项目特有的东西**：
它只说「非负且和为 1 的权重，其加权平均落在被加权量的最小与最大之间」。

**所以它是通用的。** 放在 `Attention/` 下是因为第一次需要它的是 attention，
**但它会被任何凸组合结构复用**（注意力头混合、模型平均、蒸馏的温度混合、随机策略的期望）。

## 要证什么

    m ≤ ∑ j, p j * w j ∧ ∑ j, p j * w j ≤ M

前提是 `0 ≤ p j`、`∑ p j = 1`、`∀ j, m ≤ w j`、`∀ j, w j ≤ M`。

**两侧的证明结构相同**：把常数写成 `c = ∑ j, p j * c`（用 `∑ p = 1`），
然后逐项比较（用 `p j ≥ 0`）。**没有用到任何分析学，纯粹是求和与乘法的单调性。**
-/

namespace Lattice.Lib.Attention

open Finset

/-- ⭐ **凸组合落在极值之间**：非负且和为 1 的权重，其加权平均被上下界夹住。

**这是「概率分布的期望落在支撑的凸包内」的标量版本**，
而它正是 attention 输出有界的原因——那里 `p` 是 softmax 权重、`w` 是 `V x` 的分量。 -/
theorem convex_combination_between {ι : Type*} [Fintype ι] [Nonempty ι]
    (p w : ι → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    {m M : ℝ} (hm : ∀ j, m ≤ w j) (hM : ∀ j, w j ≤ M) :
    m ≤ ∑ j, p j * w j ∧ ∑ j, p j * w j ≤ M := by
  constructor
  · -- `m = ∑ j, p j * m`, and each term is dominated by `p j * w j`
    have h1 : m = ∑ j, p j * m := by
      rw [← Finset.sum_mul, hp1, one_mul]
    rw [h1]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hm j) (hp0 j))
  · -- `M = ∑ j, p j * M`, and each term dominates `p j * w j`
    have h2 : M = ∑ j, p j * M := by
      rw [← Finset.sum_mul, hp1, one_mul]
    rw [h2]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hM j) (hp0 j))

/-! ⚠ **一条被删掉的引理**：初稿写了 `convex_combination_nonneg`，用 `m = 0, M = 0` 从上一条导出。
**那要求 `hM : ∀ j, w j ≤ 0`**——与 `hw : 0 ≤ w j` 一起把 `w` 逼成零函数。
**所以它要么是空论，要么陈述错了。** 而"非负加权量的凸组合非负"本来就是
`Finset.sum_nonneg` 加 `mul_nonneg`，不需要一条有名字的定理。**删掉，不留噪声。** -/

/-- ⭐⭐ **加权平均的 Lipschitz 性**：若每个分量差不超过 `M`，则加权平均的差也不超过 `M`。

**与上一条同一个主题**（权重非负、和为 1），但谈的是**差分**而不是**界**。
它们合起来说明：凸组合在值上是内插、在扰动上是稳定。

**证明只有两步**：把差写成 `∑ j, p j * (w j - w' j)`（用分配律），
再 `|∑| ≤ ∑ |·| = ∑ p j * |w j - w' j| ≤ ∑ p j * M = M`。**没有用到任何分析学。** -/
theorem weighted_average_lipschitz {ι : Type*} [Fintype ι] [Nonempty ι]
    (p w w' : ι → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    {M : ℝ} (hM : ∀ j, |w j - w' j| ≤ M) :
    |∑ j, p j * w j - ∑ j, p j * w' j| ≤ M := by
  -- the difference is the weighted sum of the differences
  have hkey : ∑ j, p j * w j - ∑ j, p j * w' j = ∑ j, p j * (w j - w' j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hkey]
  calc |∑ j, p j * (w j - w' j)|
      ≤ ∑ j, |p j * (w j - w' j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, p j * |w j - w' j| := by
        exact Finset.sum_congr rfl (fun j _ => by rw [abs_mul, abs_of_nonneg (hp0 j)])
    _ ≤ ∑ j, p j * M :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hM j) (hp0 j))
    _ = (∑ j, p j) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hp1, one_mul]

/-- ⭐⭐ **权重被扰动时加权平均的变化**——上一引理的对偶。

上一轮 `weighted_average_lipschitz` 谈的是「**值**变了、权重不变」；
这一条谈「**权重**变了、值不变」。**两者合起来才是加权平均在两个自变量上的完整稳定性。**

界是 `M * ∑ j, |w j|`——**对 `j` 求和而不是取最大**。技术上更松（真紧的是 `M * max_j |w j|`），
**但它避免引入 `Finset.sup`**，而一条能用的界比一条要额外机器才能陈述的紧界更有价值。 -/
theorem weighted_average_weights_lipschitz {ι : Type*} [Fintype ι] [Nonempty ι]
    (p p' w : ι → ℝ) {M : ℝ} (hM : ∀ j, |p j - p' j| ≤ M) :
    |∑ j, p j * w j - ∑ j, p' j * w j| ≤ M * ∑ j, |w j| := by
  have hkey : ∑ j, p j * w j - ∑ j, p' j * w j = ∑ j, (p j - p' j) * w j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hkey]
  calc |∑ j, (p j - p' j) * w j|
      ≤ ∑ j, |(p j - p' j) * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |p j - p' j| * |w j| :=
        Finset.sum_congr rfl (fun j _ => by rw [abs_mul])
    _ ≤ ∑ j, M * |w j| :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hM j) (abs_nonneg _))
    _ = M * ∑ j, |w j| := by rw [Finset.mul_sum]

end Lattice.Lib.Attention
