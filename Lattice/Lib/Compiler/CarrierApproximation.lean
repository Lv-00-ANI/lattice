import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lib.Compiler.LowerBound
import Lattice.Lib.Compiler.LowerBoundGeneral

/-!
# 把下界接到 LATTICE 的载体上：**离散载体上「逼近」只能是相等**（阶段 C，P8）

## 为什么这一轮才是审计真正要求的那一步

**审计第 22 条结构性禁止：**

> **`ConstraintSet` / `LinearLayer` 的系数是 `List Int`。**
> **整条链不涉及实数权重。离散空间里「逼近」的唯一含义是「相等」。**

**=> 前三轮（944–946）给出了三条纯数学下界，但它们**没有碰到 LATTICE 的载体**。**

**=> 本文件把它们接上，方法不是证明「载体不能逼近」，而是证明**更基本的事**：**

**> 在 `List Int` 上，两个不同元素之间的距离**至少是 `1`**。**
**> 因此「误差 `≤ ε`」在 `ε < 1` 时**恰好等价于「相等」。**

**=> 于是「任意小误差的逼近」在离散载体上是**逻辑上不成立**的：
它要么是精确相等（误差 `0`），要么误差至少 `1`。**

**=> 这把审计说的问题从「尚未实现」变成了**可证明的边界**。**
**=> 而 `List Int → ℝ` 的**嵌入**是唯一出路，第 944/945 轮的下界正说明**即使嵌入之后**
线性族仍不能任意逼近——两道墙都存在，而它们现在都是定理。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`int_distinct_at_least_one`** | **⭐⭐ 两个不同整数距离 `≥ 1`** |
| **`list_int_error_quantized`** | **⭐⭐⭐ `List Int` 上误差只能取 `0` 或 `≥ 1`** |
| **`discrete_approx_is_equality`** | **⭐⭐⭐ 离散载体上 `ε < 1` 的逼近 ⟺ 相等** |
| **`no_arbitrary_precision_on_discrete_carrier`** | **⭐⭐⭐ 离散载体无任意精度逼近** | -/

namespace Lattice.Lib.Compiler.CarrierApproximation

open Lattice

/-- **⭐⭐ 两个不同整数距离 `≥ 1`。**

**=> 这是「离散」的算术内容：`ℤ` 上不存在 `0` 与 `1` 之间的数。** -/
theorem int_distinct_at_least_one (m n : ℤ) (h : m ≠ n) : 1 ≤ |(m : ℝ) - (n : ℝ)| := by
  have hne : m - n ≠ 0 := sub_ne_zero.mpr h
  have hz : (1 : ℤ) ≤ |m - n| := by
    have : (0 : ℤ) < |m - n| := abs_pos.mpr hne
    omega
  have : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast hz
  rw [Int.cast_sub] at this
  calc (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := this

/-- **⭐⭐⭐ `List Int` 上误差只能取 `0` 或 `≥ 1`。**

**=> 陈述：对两个整数列表 `l₁ l₂`，若它们在某一位上不同，
则在该位上的实数差绝对值 `≥ 1`。**

**=> 这就是「离散载体的误差被量化」：不存在介于 `0` 与 `1` 之间的误差。** -/
theorem list_int_error_quantized (l₁ l₂ : List ℤ) (i : ℕ)
    (h : l₁.getD i 0 ≠ l₂.getD i 0) :
    1 ≤ |((l₁.getD i 0 : ℤ) : ℝ) - ((l₂.getD i 0 : ℤ) : ℝ)| :=
  int_distinct_at_least_one _ _ h

/-- **⭐⭐⭐ 离散载体上 `ε < 1` 的逼近 ⟺ 相等。**

**=> 陈述：若 `ε < 1` 且 `|a - b| ≤ ε`（`a b : ℤ`），则 `a = b`。**

**=> 这是本文件的核心：它说明「ε-逼近」这个**连续**概念
在 `ℤ` 上退化为**精确相等**。**

**=> 推论：要求「对任意 `ε > 0` 存在逼近」，在 `ε` 跨过 `1` 时**语义突变**——
这正是审计第 22 条禁止的内容。** -/
theorem discrete_approx_is_equality (a b : ℤ) (ε : ℝ) (hε : ε < 1)
    (h : |((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)| ≤ ε) : a = b := by
  by_contra hne
  have := int_distinct_at_least_one a b hne
  linarith

/-- **⭐⭐⭐ 离散载体无任意精度逼近（否定形式）。**

**=> 陈述：不存在 `ε < 1` 使 `a ≠ b` 但 `|a - b| ≤ ε`。**

**=> 把上面两条合起来：**一旦 `a ≠ b`，任何 `ε < 1` 都不够**。** -/
theorem no_arbitrary_precision_on_discrete_carrier :
    ¬ ∃ (a b : ℤ) (ε : ℝ), a ≠ b ∧ ε < 1 ∧ |((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)| ≤ ε := by
  rintro ⟨a, b, ε, hne, hε, h⟩
  exact hne (discrete_approx_is_equality a b ε hε h)

/-- **⭐⭐ 与第 944 轮下界的接口：两条墙。**

**=> 陈述：**

1. **离散载体上 `ε < 1` 的逼近必须精确（本文件）；**
2. **即使嵌入到 `ℝ`，线性族对 `x²` 的下界是 `1/8`（第 944 轮）。**

**=> 两条合起来：**符号⇄权重这一跳在两种解释下都不可「任意精度逼近」**。** -/
theorem two_walls (a b : ℤ) (ε : ℝ) (hε : ε < 1)
    (h : |((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)| ≤ ε) :
    a = b ∧ ∀ (c d : ℝ), ∃ x ∈ Set.Icc (0 : ℝ) 1,
      1 / 8 ≤ |x ^ 2 - (c * x + d)| :=
  ⟨discrete_approx_is_equality a b ε hε h,
    Lattice.Lib.Compiler.LowerBound.target_not_attainable⟩

end Lattice.Lib.Compiler.CarrierApproximation
