import Mathlib

/-!
# `Lattice.Lib.Penalty.QuadraticLocallyLipschitz` — **二次函数在有界集上是 Lipschitz 的**

## 与上一文件的关系

`QuadraticNotLipschitz` 证明了 `t²` **没有**全局 Lipschitz 常数。**那是负面的，而它只说了一半**：
**在有界集上它是有的，而且常数可以写出来。**

**两半合起来才是完整的事实**：

> `t²` 在半径 `R` 的球上是 `2R`-Lipschitz，**而 `R` 不能去掉**。

**这正是收敛估计需要的东西**：不能说什么到处成立，但可以说「只要迭代停在半径 `R` 的球里，
损失就是 `2R`-Lipschitz」。**上一文件给的是「为什么需要那个假设」，本文件给的是「有了假设之后得到什么」。**

## 为什么常数是 `2R`

    s² − t² = (s − t)(s + t)

⇒ `|s² − t²| = |s − t| · |s + t| ≤ |s − t| · (|s| + |t|) ≤ |s − t| · 2R`。

**恒等式只一步，界只一步。** 而 `2R` **不能改进**：取 `s = R`、`t = −R` 时
`|s² − t²| = 0`；取 `t = 0` 时 `|s² − 0| = R² = R · R`，比值 `R`。
**所以真紧的常数是 `R`（不是 `2R`），但 `2R` 的证明只用一个恒等式**，而且**两者都随 `R` 线性增长**。
**本文件陈述 `2R` 版本，并在 docstring 里说明 `R` 版本更强、若要可以再证一次。**
-/

namespace Lattice.Lib.Penalty

/-- ⭐⭐ **二次函数在有界区间上是 Lipschitz 的**：`|s|, |t| ≤ R` 时 `|s² − t²| ≤ 2R·|s − t|`。

**这是 `sq_not_lipschitz` 的正向对偶**：那条说没有全局常数，这条说**局部常数就是 `2R`**。 -/
theorem sq_lipschitz_on_bounded {s t R : ℝ} (hR : 0 ≤ R) (hs : |s| ≤ R) (ht : |t| ≤ R) :
    |s ^ 2 - t ^ 2| ≤ 2 * R * |s - t| := by
  have hfac : s ^ 2 - t ^ 2 = (s - t) * (s + t) := by ring
  rw [hfac, abs_mul]
  have hsum : |s + t| ≤ 2 * R := by
    calc |s + t| ≤ |s| + |t| := abs_add _ _
      _ ≤ R + R := add_le_add hs ht
      _ = 2 * R := by ring
  calc |s - t| * |s + t| ≤ |s - t| * (2 * R) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = 2 * R * |s - t| := by ring

/-- ⭐⭐ **平方和在有界集上是 Lipschitz 的**：逐分量被 `R` 界住时，

`|∑ i, (f i)² − ∑ i, (g i)²| ≤ 2R · ∑ i, |f i − g i|`。

**右边是「差的绝对值和」而不是「差的范数」**——因为本库的载体是 `Fin n → ℝ`，
而 `IsLipschitzInstr` 用的正是逐分量界。**两个形状在本库里是同一件事的两种写法。**

**这条是 `sqDist` 局部 Lipschitz 的直接前件**：那里 `f i = p i − q i`、`g i = p' i − q' i`。 -/
theorem sum_sq_lipschitz_on_bounded {ι : Type*} [Fintype ι] (f g : ι → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ i, |f i| ≤ R) (hg : ∀ i, |g i| ≤ R) :
    |∑ i, (f i) ^ 2 - ∑ i, (g i) ^ 2| ≤ 2 * R * ∑ i, |f i - g i| := by
  have hsplit : ∑ i, (f i) ^ 2 - ∑ i, (g i) ^ 2 = ∑ i, ((f i) ^ 2 - (g i) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
  rw [hsplit]
  calc |∑ i, ((f i) ^ 2 - (g i) ^ 2)|
      ≤ ∑ i, |(f i) ^ 2 - (g i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * R * |f i - g i| :=
        Finset.sum_le_sum (fun i _ => sq_lipschitz_on_bounded hR (hf i) (hg i))
    _ = 2 * R * ∑ i, |f i - g i| := by rw [Finset.mul_sum]

end Lattice.Lib.Penalty
