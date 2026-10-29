import Mathlib
import Lattice.Lib.Attention.SoftmaxLipschitz

/-!
# softmax 的 Lipschitz 界（无条件）

## 结论

    |softmax z i − softmax z' i| ≤ 2·ε·exp (2·ε)        ∀ j, |z j − z' j| ≤ ε

**没有对分数的下界假设。** 第 46 轮的文档估计需要「分数的下界 `m`」——那条路是**分母直接放大**；
本节走的是**逐点比值**，而比值是一个**加权平均**，权重是 `softmax z`（非负、和为 1），**所以不需要下界**。

## 证明的三步

1. **分子的比**：`exp (z i) / exp (z' i) = exp (z i − z' i) ≤ exp ε`；
2. **分母的比**：`(∑ exp z')/(∑ exp z) = ∑ j, softmax z j · exp (z' j − z j) ≤ exp ε`
   ——**这是加权平均**，每个因子 `≤ exp ε`、权重和为 1；
3. 两者相乘得 `softmax z i / softmax z' i ≤ exp (2ε)`，再由 `softmax ≤ 1` 与
   `exp t − 1 ≤ t·exp t`（`SoftmaxLipschitz.exp_sub_one_le`）收尾。

**第 3 步的最后一句复用了第 46 轮的定理**——本轮的界不是凭空的，它建在那条的 `exp` 估计上。 -/

namespace Lattice.Lib.Attention

open Lattice

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- 分母恒正。 -/
theorem sum_exp_pos (z : ι → ℝ) : 0 < ∑ j, Real.exp (z j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- `softmax z i = exp (z i) / ∑ j, exp (z j)`，按定义展开。 -/
theorem softmax_eq (z : ι → ℝ) (i : ι) :
    softmax z i = Real.exp (z i) / ∑ j, Real.exp (z j) := rfl

/-- **`softmax` 每一项严格为正**。 -/
theorem softmax_pos (z : ι → ℝ) (i : ι) : 0 < softmax z i := by
  rw [softmax_eq]
  exact div_pos (Real.exp_pos _) (sum_exp_pos z)

/-- ⭐ **`B/A` 是加权平均**：`(∑ exp z')/(∑ exp z) = ∑ j, softmax z j · exp (z' j − z j)`。 -/
theorem sum_ratio (z z' : ι → ℝ) :
    (∑ j, Real.exp (z' j)) / (∑ j, Real.exp (z j))
      = ∑ j, softmax z j * Real.exp (z' j - z j) := by
  have hA : (∑ j, Real.exp (z j)) ≠ 0 := ne_of_gt (sum_exp_pos z)
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [softmax_eq, Real.exp_sub]
  field_simp
  ring

/-- ⭐⭐ **`B/A ≤ exp ε`**：权重非负、和为 1，每项 `≤ exp ε`。 -/
theorem sum_ratio_le (z z' : ι → ℝ) (ε : ℝ) (h : ∀ j, |z j - z' j| ≤ ε) :
    (∑ j, Real.exp (z' j)) / (∑ j, Real.exp (z j)) ≤ Real.exp ε := by
  rw [sum_ratio]
  have hbound : ∀ j ∈ (Finset.univ : Finset ι), Real.exp (z' j - z j) ≤ Real.exp ε := by
    intro j _
    apply Real.exp_le_exp.mpr
    have h1 := (abs_le.mp (h j)).1
    have h2 := (abs_le.mp (h j)).2
    linarith
  calc ∑ j, softmax z j * Real.exp (z' j - z j)
      ≤ ∑ j, softmax z j * Real.exp ε := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hbound j (Finset.mem_univ j)) (softmax_nonneg z j)
    _ = (∑ j, softmax z j) * Real.exp ε := by rw [Finset.sum_mul]
    _ = Real.exp ε := by rw [softmax_sum_one]; ring

/-- ⭐⭐ **比值界**：`softmax z i / softmax z' i ≤ exp (2ε)`。 -/
theorem softmax_ratio_le (z z' : ι → ℝ) (ε : ℝ) (h : ∀ j, |z j - z' j| ≤ ε) (i : ι) :
    softmax z i / softmax z' i ≤ Real.exp (2 * ε) := by
  have hnum : Real.exp (z i) / Real.exp (z' i) ≤ Real.exp ε := by
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (h i)).2
    linarith
  have hden : (∑ j, Real.exp (z' j)) / (∑ j, Real.exp (z j)) ≤ Real.exp ε := sum_ratio_le z z' ε h
  have hA := sum_exp_pos z
  have hB := sum_exp_pos z'
  have hkey : softmax z i / softmax z' i
      = (Real.exp (z i) / Real.exp (z' i)) * ((∑ j, Real.exp (z' j)) / (∑ j, Real.exp (z j))) := by
    rw [softmax_eq, softmax_eq]
    field_simp
    ring
  rw [hkey]
  calc (Real.exp (z i) / Real.exp (z' i)) * ((∑ j, Real.exp (z' j)) / (∑ j, Real.exp (z j)))
      ≤ Real.exp ε * Real.exp ε :=
        mul_le_mul hnum hden (le_of_lt (div_pos hB hA)) (le_of_lt (Real.exp_pos ε))
    _ = Real.exp (2 * ε) := by rw [← Real.exp_add]; ring_nf

/-- ⭐⭐⭐ **softmax 的 Lipschitz 界**：`|softmax z i − softmax z' i| ≤ 2ε·exp (2ε)`，
`ε` 是分数**逐点差**的界。**无条件成立。** -/
theorem softmax_lipschitz (z z' : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ j, |z j - z' j| ≤ ε) (i : ι) :
    |softmax z i - softmax z' i| ≤ 2 * ε * Real.exp (2 * ε) := by
  have hsym : ∀ j, |z' j - z j| ≤ ε := by
    intro j; rw [abs_sub_comm]; exact h j
  -- a difference bound from a ratio bound
  have key : ∀ (a b : ℝ), 0 < b → b ≤ 1 → a / b ≤ Real.exp (2 * ε) →
      a - b ≤ Real.exp (2 * ε) - 1 := by
    intro a b hb hb1 hr
    have h1 : a ≤ b * Real.exp (2 * ε) := by
      have hm := mul_le_mul_of_nonneg_right hr (le_of_lt hb)
      field_simp at hm
      linarith
    -- `exp (2ε) ≥ 1` uses `ε ≥ 0`
    have hexp1 : 1 ≤ Real.exp (2 * ε) := by
      have h2 : Real.exp 0 ≤ Real.exp (2 * ε) := Real.exp_le_exp.mpr (by linarith)
      simpa using h2
    nlinarith
  have hfin : Real.exp (2 * ε) - 1 ≤ 2 * ε * Real.exp (2 * ε) := exp_sub_one_le (2 * ε)
  rcases le_total (softmax z' i) (softmax z i) with hle | hle
  · have h1 := key (softmax z i) (softmax z' i) (softmax_pos z' i) (softmax_le_one z' i)
      (softmax_ratio_le z z' ε h i)
    rw [abs_of_nonneg (by linarith)]
    exact h1.trans hfin
  · have h1 := key (softmax z' i) (softmax z i) (softmax_pos z i) (softmax_le_one z i)
      (softmax_ratio_le z' z ε hsym i)
    rw [abs_of_nonpos (by linarith), neg_sub]
    exact h1.trans hfin

end Lattice.Lib.Attention
