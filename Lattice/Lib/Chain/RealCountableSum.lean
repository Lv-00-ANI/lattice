import Mathlib
import Lattice.Lib.LinearAlgebra.RealInfiniteDim
/-!
# LATTICE: 有限类型 → 可数和的桥接、`tsum` 版 Cauchy–Schwarz、乘积和分解

`RealInfiniteDim` 已给出「非负列的所有有限截断一致有界 ⟹ 可和且界保持」这一
**半成品桥**（`infinite_sum_bound`）。本文件把它从 `ℕ` 提升到**任意指标类型**，
并把实 Cauchy–Schwarz 从有限和推广到 `tsum`：

  1. `finite_sum_le_tsum_general`：`f : ι → ℝ` 非负，且**所有**有限集
     `s` 都有 `∑_{i∈s} f i ≤ C` ⟹ `Summable f ∧ ∑' i, f i ≤ C`
     （`summable_of_sum_le` + `tsum_le_of_sum_le`）——`infinite_sum_bound` 的任意指标版；
  2. `finset_bound_to_tsum`：`ℕ` 上「range 截断一致有界」⟹ 可和且界保持，
     **直接引用（复述）`RealInfiniteDim.infinite_sum_bound`**，不重新定义同名结论；
  3. `le_tsum_of_nonneg`、`summable_sq_of_nonneg`、`summable_mul_of_nonneg`：
     非负可和列的单项界与平方/乘积可和性（为 `tsum` CS 铺路）；
  4. **`tsum` 版 Cauchy–Schwarz**（非负、可和、完整证明）：
     `tsum_mul_sq_le_sq_mul_tsum :
       (∑' i, f i * g i)^2 ≤ (∑' i, f i^2) * (∑' i, g i^2)`
     证明路线：对每个有限 `s` 用实 CS `Finset.sum_mul_sq_le_sq_mul_sq`，
     再用 `sum_le_tsum` 把 `∑_{i∈s} f i^2` 控制到 `∑' i, f i^2`，
     得 `∑_{i∈s} f i g i ≤ sqrt(∑' f²)·sqrt(∑' g²)` 对一切有限 `s` 成立，
     最后用 `tsum_le_of_sum_le` 取上确界并平方；
  5. 乘积和分解：`tsum_prod_factor`
     `∑' p : ι × κ, f p.1 * g p.2 = (∑' i, f i) * (∑' j, g j)`
     （`tsum_mul_tsum` 的 `ι × κ` 推论，需显式给出逐点乘积可和）、
     `tsum_prod_pair_tsum`（`∑' p, f p.1 * g p.2 = ∑' i, ∑' j, f i * g j`，`tsum_prod`）、
     以及 `tsum_prod_tsum`（`∑' p, f p.1 p.2 = ∑' i, ∑' j, f i j`，`tsum_prod`）；
  6. `tsum_le_of_uniform_finset_bound` / `tsum_le_of_uniform_finset_bound_general`：
     一致有限集界直接给出无穷和的界，其中前者**显式复用 `RealInfiniteDim.infinite_sum_bound`**。

诚实标注（无 sorry / axiom / admit）：
- 本文件的 `tsum` Cauchy–Schwarz 是**非负、可和**范围内的完整结论；一般（有符号）
  可和列的 `tsum` CS 未证/未做（一般情形需 ℓ² 内积空间的 Cauchy–Schwarz，
  本文件不引入 Hilbert 空间机器）——属于**降级**：结论只在非负锥上成立；
- 未做：不可和列的部分和发散情形、`tsum` 的条件收敛重排、`tsum` 的绝对收敛判别；
- `finite_sum_le_tsum_general` 不含可数性假设（mathlib 的 `summable_of_sum_le`
  对任意指标类型成立）；本文件不声称任何不可数指标上的可和性额外结论；
- `RealInfiniteDim` 提供半成品桥（只读引用），本文件在其上完成 `ℕ → 任意指标`
  与 `有限和 → tsum` 两个方向的提升。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {ι : Type*}

/-! ## 一、有限集一致界 ⟹ 可和且界保持（任意指标类型） -/

/-- **有限集一致界 ⟹ 可和且界保持（一般指标类型）**：
非负 `f : ι → ℝ`，若**所有**有限集 `s` 满足 `∑_{i∈s} f i ≤ C`，
则 `f` 可和且 `∑' i, f i ≤ C`。
（`summable_of_sum_le` 给可和性，`tsum_le_of_sum_le` 给界的极限保持。） -/
theorem finite_sum_le_tsum_general (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (C : ℝ)
    (hC : ∀ s : Finset ι, ∑ i in s, f i ≤ C) :
    Summable f ∧ ∑' i, f i ≤ C :=
  ⟨summable_of_sum_le hf hC, tsum_le_of_sum_le (summable_of_sum_le hf hC) hC⟩

/-- **`RealInfiniteDim` 半成品桥的复述（只读复用）**：`ℕ` 上非负列的所有
`range` 截断一致有界 ⟹ 可和且界保持。本定理**不重新证明**，而是直接引用
`RealInfiniteDim.infinite_sum_bound`，把它作为本文件的入口桥。
（诚实标注：此结论的证明属于 `RealInfiniteDim`，本文件仅复用。） -/
theorem finset_bound_to_tsum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (C : ℝ)
    (hC : ∀ N : ℕ, ∑ n in Finset.range N, a n ≤ C) :
    Summable a ∧ ∑' n, a n ≤ C :=
  infinite_sum_bound a ha C hC

/-! ## 二、非负可和列的基础工具 -/

/-- 非负可和列中每一项被无穷和控制：`f i ≤ ∑' i, f i`。 -/
theorem le_tsum_of_nonneg (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hfs : Summable f) (i : ι) :
    f i ≤ ∑' i, f i :=
  le_tsum hfs i (fun j _ => hf j)

/-- 非负可和列 ⟹ 其平方列可和（用 `∑' f` 作为逐点界与优级数）。 -/
theorem summable_sq_of_nonneg (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hfs : Summable f) :
    Summable (fun i => f i ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg (f i)) (fun i => ?_)
    (hfs.mul_left (∑' i, f i))
  calc f i ^ 2 = f i * f i := by ring
    _ ≤ (∑' i, f i) * f i := mul_le_mul_of_nonneg_right (le_tsum_of_nonneg f hf hfs i) (hf i)

/-- 两个非负可和列 ⟹ 逐点乘积列可和。 -/
theorem summable_mul_of_nonneg (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable f) (hgs : Summable g) : Summable (fun i => f i * g i) := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hf i) (hg i)) (fun i => ?_)
    (hgs.mul_left (∑' i, f i))
  exact mul_le_mul_of_nonneg_right (le_tsum_of_nonneg f hf hfs i) (hg i)

/-! ## 三、`tsum` 版 Cauchy–Schwarz（非负、可和） -/

/-- **`tsum` 版 Cauchy–Schwarz（非负可和列）**：
`(∑' i, f i * g i)^2 ≤ (∑' i, f i^2) * (∑' i, g i^2)`。

证明：对每个有限集 `s`，实 CS 给出
`∑_{i∈s} f i g i ≤ sqrt(∑_{i∈s} f i^2) * sqrt(∑_{i∈s} g i^2)`；
由 `sum_le_tsum` 把两个有限平方和放大为 `tsum` 平方和；于是
`∑_{i∈s} f i g i ≤ sqrt(∑' f²) * sqrt(∑' g²)` 对一切有限 `s` 成立，
再用 `tsum_le_of_sum_le` 得 `∑' i, f i g i ≤ sqrt(∑' f²) * sqrt(∑' g²)`，
两边非负，平方即得。 -/
theorem tsum_mul_sq_le_sq_mul_tsum (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable f) (hgs : Summable g) :
    (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * (∑' i, g i ^ 2) := by
  have hf2 : Summable (fun i => f i ^ 2) := summable_sq_of_nonneg f hf hfs
  have hg2 : Summable (fun i => g i ^ 2) := summable_sq_of_nonneg g hg hgs
  have hfg : Summable (fun i => f i * g i) := summable_mul_of_nonneg f g hf hg hfs hgs
  have hmain : ∑' i, f i * g i
      ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
    apply tsum_le_of_sum_le hfg
    intro s
    have hnn : 0 ≤ ∑ i in s, f i * g i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (hg i))
    have h1 : (∑ i in s, f i * g i)
        ≤ Real.sqrt (∑ i in s, f i ^ 2) * Real.sqrt (∑ i in s, g i ^ 2) := by
      calc ∑ i in s, f i * g i
          = Real.sqrt ((∑ i in s, f i * g i) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
        _ ≤ Real.sqrt ((∑ i in s, f i ^ 2) * (∑ i in s, g i ^ 2)) :=
            Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq s f g)
        _ = Real.sqrt (∑ i in s, f i ^ 2) * Real.sqrt (∑ i in s, g i ^ 2) :=
            Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (f i))) _
    calc ∑ i in s, f i * g i
        ≤ Real.sqrt (∑ i in s, f i ^ 2) * Real.sqrt (∑ i in s, g i ^ 2) := h1
      _ ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) :=
          mul_le_mul
            (Real.sqrt_le_sqrt (sum_le_tsum s (fun i _ => sq_nonneg (f i)) hf2))
            (Real.sqrt_le_sqrt (sum_le_tsum s (fun i _ => sq_nonneg (g i)) hg2))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc (∑' i, f i * g i) ^ 2
      ≤ (Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg (fun i => mul_nonneg (hf i) (hg i))) hmain 2
    _ = (∑' i, f i ^ 2) * (∑' i, g i ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg (f i))),
            Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg (g i)))]

/-! ## 四、乘积和分解 -/

/-- **乘积和分解（`tsum_mul_tsum` 的 `ι × κ` 形式）**：对可和实列 `f`、`g` 及可和的
逐点乘积 `(p ↦ f p.1 * g p.2)`，有
`∑' p : ι × κ, f p.1 * g p.2 = (∑' i, f i) * (∑' j, g j)`。 -/
theorem tsum_prod_factor {κ : Type*} (f : ι → ℝ) (g : κ → ℝ)
    (hf : Summable f) (hg : Summable g)
    (hfg : Summable (fun p : ι × κ => f p.1 * g p.2)) :
    ∑' p : ι × κ, f p.1 * g p.2 = (∑' i, f i) * (∑' j, g j) :=
  (tsum_mul_tsum hf hg hfg).symm

/-- **乘积和分解（迭代和形式）**：在逐点乘积可和的前提下，`ι × κ` 上的和等于迭代和
`∑' p : ι × κ, f p.1 * g p.2 = ∑' i, ∑' j, f i * g j`（`tsum_prod`）。
这是 `tsum_prod_factor` 的「先坐标展开」版本，专门证明乘积和的迭代结构。 -/
theorem tsum_prod_pair_tsum {κ : Type*} (f : ι → ℝ) (g : κ → ℝ)
    (hfg : Summable (fun p : ι × κ => f p.1 * g p.2)) :
    ∑' p : ι × κ, f p.1 * g p.2 = ∑' i, ∑' j, f i * g j :=
  tsum_prod hfg

/-- **二重和的乘积型展开**：可和二元函数按坐标的迭代和
`∑' p : ι × κ, f p.1 p.2 = ∑' i, ∑' j, f i j`（`tsum_prod`）。 -/
theorem tsum_prod_tsum {κ : Type*} (f : ι → κ → ℝ)
    (h : Summable (fun p : ι × κ => f p.1 p.2)) :
    ∑' p : ι × κ, f p.1 p.2 = ∑' i, ∑' j, f i j :=
  tsum_prod h

/-! ## 五、一致有限集界直接控制无穷和 -/

/-- **一致有限集界 ⟹ 无穷和界（`ℕ` 版，显式复用 `RealInfiniteDim`）**：
非负列 `a : ℕ → ℝ` 的所有 `range` 截断一致有界 `≤ C` ⟹ `∑' n, a n ≤ C`。
本定理的证明**直接取 `RealInfiniteDim.infinite_sum_bound` 的第二分量**，
即 `RealInfiniteDim` 提供的半成品桥在此被再次复用（只读）。 -/
theorem tsum_le_of_uniform_finset_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (C : ℝ)
    (hC : ∀ N : ℕ, ∑ n in Finset.range N, a n ≤ C) :
    (∑' n, a n) ≤ C :=
  (infinite_sum_bound a ha C hC).2

/-- **一致有限集界 ⟹ 无穷和界（一般指标类型版）**：
`finite_sum_le_tsum_general` 的第二分量，把 `ℕ` 上的桥提升到任意 `ι`。 -/
theorem tsum_le_of_uniform_finset_bound_general (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (C : ℝ)
    (hC : ∀ s : Finset ι, ∑ i in s, f i ≤ C) :
    (∑' i, f i) ≤ C :=
  (finite_sum_le_tsum_general f hf C hC).2

end Lattice
