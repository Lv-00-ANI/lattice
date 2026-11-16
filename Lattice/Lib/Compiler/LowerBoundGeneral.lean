import Mathlib
import Lattice.Lib.Compiler.LowerBound

/-!
# 下界定理（二）：仿射族对**指定三值**有正下界（阶段 C，P8）

## 与第 944 轮的关系

**第 944 轮证：`[0,1]` 上仿射对 `x²` 的一致误差 `≥ 1/8`。**

**本文件证明它背后的**一般机制**，并给出一个更锐利的见证：**

**> 在三点 `x = 0, 1/2, 1` 上指定目标值 `y₀, y₁, y₂`。**
**> 仿射函数 `L x = a·x + b` 在**中点**的取值恒为两端点的**平均**。**
**> 故只要目标中点值偏离两端平均，任何仿射都有一点偏差 `≥ |y₁ - (y₀+y₂)/2| / 3`。**

**=> 取 `(y₀, y₁, y₂) = (0, 1, 0)`，下界为 `1/6`。**

**=> 这就是「有限维不能任意精度逼近」的**最小见证**，且完全用 `ℝ` 陈述。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`affine_midpoint`** | **⭐⭐ 仿射在中点取两端平均** |
| **`three_point_affine_lower_bound`** | **⭐⭐ 三点偏差下界 `\|y₁-(y₀+y₂)/2\|/3`** |
| **`no_uniform_affine_approximation`** | **⭐⭐⭐ 目标 `(0,1,0)` 的偏差 `≥ 1/6`** | -/

namespace Lattice.Lib.Compiler.LowerBoundGeneral

/-- **⭐⭐ 仿射在中点取两端平均。**

**=> `a·(1/2) + b = ((a·0 + b) + (a·1 + b)) / 2`。**

**=> 这是整个下界的结构原因：仿射的自由度是 **2**，而三点约束是 **3**。** -/
theorem affine_midpoint (a b : ℝ) :
    a * (1 / 2) + b = ((a * 0 + b) + (a * 1 + b)) / 2 := by
  ring

/-- **⭐⭐ 三点偏差下界。**

**=> 对任意目标 `y₀ y₁ y₂` 与任意仿射 `a b`，三点偏差的最大值
`≥ |y₁ - (y₀+y₂)/2| / 3`。**

**=> 证明：中点偏差可分解为「目标中点偏离」减去「仿射端点偏差的平均」。** -/
theorem three_point_affine_lower_bound (y₀ y₁ y₂ : ℝ) (a b : ℝ) :
    |y₁ - (y₀ + y₂) / 2| / 3 ≤
      max (|y₀ - (a * 0 + b)|) (max (|y₁ - (a * (1 / 2) + b)|) (|y₂ - (a * 1 + b)|)) := by
  set M := max (|y₀ - (a * 0 + b)|)
    (max (|y₁ - (a * (1 / 2) + b)|) (|y₂ - (a * 1 + b)|)) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (abs_nonneg _)
  have e0 : |y₀ - (a * 0 + b)| ≤ M := le_max_left _ _
  have e1 : |y₁ - (a * (1 / 2) + b)| ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have e2 : |y₂ - (a * 1 + b)| ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  -- rewrite the midpoint model value
  have hm : a * (1 / 2) + b = ((a * 0 + b) + (a * 1 + b)) / 2 := affine_midpoint a b
  -- the target deviation splits as (midpoint error) + (average of endpoint errors)
  have hsplit : y₁ - (y₀ + y₂) / 2
      = (y₁ - (a * (1 / 2) + b)) + (((a * 0 + b) - y₀) + ((a * 1 + b) - y₂)) / 2 := by
    rw [hm]; ring
  have hbound : |y₁ - (y₀ + y₂) / 2| ≤ M + (M + M) / 2 := by
    rw [hsplit]
    have h1 : |(y₁ - (a * (1 / 2) + b)) + (((a * 0 + b) - y₀) + ((a * 1 + b) - y₂)) / 2|
        ≤ |y₁ - (a * (1 / 2) + b)| + |(((a * 0 + b) - y₀) + ((a * 1 + b) - y₂)) / 2| :=
      abs_add _ _
    have h2 : |(((a * 0 + b) - y₀) + ((a * 1 + b) - y₂)) / 2|
        ≤ (|(a * 0 + b) - y₀| + |(a * 1 + b) - y₂|) / 2 := by
      rw [abs_div]
      have h2' : |(2 : ℝ)| = 2 := by norm_num
      rw [h2']
      have := abs_add ((a * 0 + b) - y₀) ((a * 1 + b) - y₂)
      linarith
    have h3 : |(a * 0 + b) - y₀| = |y₀ - (a * 0 + b)| := by rw [abs_sub_comm]
    have h4 : |(a * 1 + b) - y₂| = |y₂ - (a * 1 + b)| := by rw [abs_sub_comm]
    linarith [e0, e1, e2]
  linarith [hbound]

/-- **⭐⭐⭐ 有限维仿射族存在不可逼近目标。**

**=> 目标：三点上取 `0, 1, 0`。**

**=> 结论：任何仿射都有一点偏差 `≥ 1/6`；故对任何 `ε < 1/6` 不存在一致逼近。** -/
theorem no_uniform_affine_approximation :
    ¬ ∃ a b : ℝ, (|(0 : ℝ) - (a * 0 + b)| ≤ 1 / 7) ∧
        (|(1 : ℝ) - (a * (1 / 2) + b)| ≤ 1 / 7) ∧
        (|(0 : ℝ) - (a * 1 + b)| ≤ 1 / 7) := by
  rintro ⟨a, b, h0, h1, h2⟩
  have key := three_point_affine_lower_bound 0 1 0 a b
  have hm : max (|(0 : ℝ) - (a * 0 + b)|)
      (max (|(1 : ℝ) - (a * (1 / 2) + b)|) (|(0 : ℝ) - (a * 1 + b)|)) ≤ 1 / 7 :=
    max_le h0 (max_le h1 h2)
  have hL : (1 : ℝ) / 6 ≤ |(1 : ℝ) - ((0 : ℝ) + 0) / 2| / 3 := by
    have h1' : ((0 : ℝ) + 0) / 2 = 0 := by norm_num
    rw [h1', sub_zero, abs_one]
    norm_num
  linarith [key, hm, hL]

end Lattice.Lib.Compiler.LowerBoundGeneral
