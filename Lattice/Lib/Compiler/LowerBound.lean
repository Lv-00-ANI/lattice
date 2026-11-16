import Mathlib

/-!
# 下界定理（一）：线性函数**不能**逼近平方函数（阶段 C，P8 目标重构）

## 为什么这个文件重要

**审计（第 944 轮）的判决：**

> **「项目现在的问题不是「离目标还差多少」，而是「目标被设成了一个数学上不成立的形式，
> 而项目里没有一条定理指出这一点」。」**

> **「0 条 `∀ε ∃w`、0 条 `Tendsto error`、0 条下界。」**

**=> 本文件是全库第一条**逼近下界定理**。**

## 核心论证（纯代数 + 三角不等式）

**对线性 `L x = a·x + b`，令 `E(x) = x² - (a·x + b)`。三点的值满足**

```
E(0) + E(1) - 2·E(1/2) = 1/2
```

**若三点误差都 `< ε`，则 `1/2 = E(0) + E(1) - 2·E(1/2) ≤ ε + ε + 2ε = 4ε`，
故 `ε > 1/8`。**

**=> 于是三点中必有一点误差 `≥ 1/8`，与 `a`、`b` 无关。**

**=> 这就是下界。`1/8` 也正是 `x²` 在 `[0,1]` 上与最优直线的最大偏差。** -/

namespace Lattice.Lib.Compiler.LowerBound

open Set

/-- **⭐⭐ 三点恒等式：`E(0) + E(1) - 2·E(1/2) = 1/2`。** -/
theorem three_point_identity (a b : ℝ) :
    ((0 : ℝ) ^ 2 - (a * 0 + b)) + ((1 : ℝ) ^ 2 - (a * 1 + b))
      - 2 * ((1 / 2 : ℝ) ^ 2 - (a * (1 / 2) + b)) = 1 / 2 := by
  ring

/-- **⭐⭐ 三点中至少一点误差 `≥ 1/8`。**

**=> 反证：若三点都 `< 1/8`，则由恒等式与 `|E| < 1/8` 得 `1/2 < 4·(1/8) = 1/2`。** -/
theorem one_point_error_large (a b : ℝ) :
    ∃ x ∈ Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)| := by
  by_contra h
  push_neg at h
  have h0 : |((0 : ℝ) ^ 2 - (a * 0 + b))| < 1 / 8 := h 0 (left_mem_Icc.mpr (by norm_num))
  have h1 : |((1 : ℝ) ^ 2 - (a * 1 + b))| < 1 / 8 := h 1 (right_mem_Icc.mpr (by norm_num))
  have hh : |((1 / 2 : ℝ) ^ 2 - (a * (1 / 2) + b))| < 1 / 8 :=
    h (1 / 2) (by constructor <;> norm_num)
  obtain ⟨u0l, u0r⟩ := abs_lt.mp h0
  obtain ⟨u1l, u1r⟩ := abs_lt.mp h1
  obtain ⟨uhl, uhr⟩ := abs_lt.mp hh
  have key := three_point_identity a b
  -- -(2*Ehalf) ≤ 2*|Ehalf| < 2*(1/8)
  have th : -(2 * ((1 / 2 : ℝ) ^ 2 - (a * (1 / 2) + b))) < 2 * (1 / 8) := by linarith
  linarith

/-- **⭐⭐⭐ 下界定理：不存在一致误差 `< 1/8` 的线性逼近。**

**=> 对任意 `ε < 1/8`，无 `a b` 使 `∀ x ∈ [0,1], |x² - (a·x+b)| ≤ ε`。**

**=> 这否定 R1 的一个特例：**「对一切目标、任意精度，存在权重」为假。** -/
theorem no_uniform_linear_approximation (ε : ℝ) (hε : ε < 1 / 8) :
    ¬ ∃ a b : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, |x ^ 2 - (a * x + b)| ≤ ε := by
  rintro ⟨a, b, hbound⟩
  obtain ⟨x, hx, hge⟩ := one_point_error_large a b
  have := hbound x hx
  linarith

/-- **⭐⭐⭐ 目标判决：最优一致误差有一个与 `a`、`b` 无关的正下界。**

**=> `∀ a b, ∃ x ∈ [0,1], 1/8 ≤ |x² - (a·x+b)|`。**

**=> 这就是「逼近不可能性」的最简陈述。** -/
theorem target_not_attainable :
    ∀ a b : ℝ, ∃ x ∈ Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)| :=
  one_point_error_large

end Lattice.Lib.Compiler.LowerBound
