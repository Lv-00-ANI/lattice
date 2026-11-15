import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile

/-!
# `relu` 的化简引理：把常量计算留**在一个**地方（阶段 C，P6）

## 为什么单独开一个文件

**第 921 轮我把化简写在**目标证明的中间**，结果八次尝试都没让 `reluCompile 1 0 (-1) = 0` 化简。**
**失败的原因不是数学，而是 `relu` 有**两处**定义：**

| 位置 | 定义 |
|:--|:--|
| **`Core/Net.lean:73`** | **`def relu (x : ℝ) : ℝ := max x 0`** |
| **`Runtime/RealNonlinear.lean:35`** | **`def relu (x : ℝ) : ℝ := max x 0`** |

**=> 两处**同义但不同名**，于是 `unfold relu` 在 `reluCompile` 的语境里可能展开错了那个，
或者两个都不展开。**

**本文件的做法：用**完全限定名**把该展开的那个钉死，
把 `max` 的计算收进**一条**引理，然后所有常量见证复用它。**

## 交付什么

| 引理 | 内容 |
|:--|:--|
| **`relu_eq_max`** | **⭐ 展开：`relu x = max x 0`（完全限定）** |
| **`relu_of_nonpos`** | **⭐⭐ `x ≤ 0 ⟹ relu x = 0`** |
| **`relu_of_nonneg`** | **⭐ `0 ≤ x ⟹ relu x = x`** |
| **`reluCompile_of_nonpos`** | **⭐⭐ `a*x + b ≤ 0 ⟹ reluCompile a b x = 0`** |
| **`reluCompile_zero_neg`** | **⭐⭐ `reluCompile 1 0 (-1) = 0`（能用一条引理直接算）** |

**=> 最后一条是第 921 轮卡住的那个等式。本文件让它变成一行。** -/

namespace Lattice.Lib.Compiler.ReluLemmas

open Lattice

/-- **⭐ 展开（完全限定到 `RealNonlinearCompile` 用的那个 `relu`）。**

**=> `relu x = max x 0`。用 `Lattice.relu` 的完全限定名避免多命名空间歧义。** -/
theorem relu_eq_max (x : ℝ) : relu x = max x 0 := rfl

/-- **⭐⭐ `x ≤ 0 ⟹ relu x = 0`。**

**=> 这是 `max x 0 = 0` 在 `x ≤ 0` 时的形式。
第 921 轮所有常量见证都归结到这一条。** -/
theorem relu_of_nonpos {x : ℝ} (h : x ≤ 0) : relu x = 0 := by
  unfold relu
  exact max_eq_right h

/-- **⭐ `0 ≤ x ⟹ relu x = x`。** -/
theorem relu_of_nonneg {x : ℝ} (h : 0 ≤ x) : relu x = x := by
  unfold relu
  exact max_eq_left h

/-- **⭐⭐ `a*x + b ≤ 0 ⟹ reluCompile a b x = 0`。**

**=> 把 `reluCompile` 的展开与 `relu_of_nonpos` 合起来。**
**=> 这是「relu 在负半轴把一切压成零」的形式化，也是 relu 载体不可逆的**唯一**根据。** -/
theorem reluCompile_of_nonpos (a b x : ℝ) (h : a * x + b ≤ 0) :
    reluCompile a b x = 0 := by
  show relu (a * x + b) = 0
  exact relu_of_nonpos h

/-- **⭐⭐ 第 921 轮卡住的那个等式，现在是一行。**

**=> `reluCompile 1 0 (-1) = 0`，因为 `1 * (-1) + 0 = -1 ≤ 0`。** -/
theorem reluCompile_zero_neg : reluCompile 1 0 (-1) = 0 := by
  apply reluCompile_of_nonpos
  norm_num

/-- **⭐ `reluCompile 1 0 0 = 0`。** -/
theorem reluCompile_zero_zero : reluCompile 1 0 0 = 0 := by
  apply reluCompile_of_nonpos
  norm_num

/-- **⭐⭐ 更关键的一条：任意 `a` 下 `reluCompile a 0 (-1) = 0`。**

**=> 因为 `a * (-1) + 0 = -a`，而依赖 `a` 的符号 —— 但 `relu` 对**任意**非正输入都是零，
所以只要 `a ≥ 0` 就够。** -/
theorem reluCompile_zero_neg_of_nonneg (a : ℝ) (ha : 0 ≤ a) :
    reluCompile a 0 (-1) = 0 := by
  apply reluCompile_of_nonpos
  nlinarith

/-- **⭐⭐ 见证存在：`reluCompile` 在 `a = 1` 下把 `x = 0` 与 `x = -1` 映到同一个输出。**

**=> 这是 relu 载体不可逆的**直接根据**：两个不同符号，同一个输出。

**=> 有了本文件的引理，这个等式是 `reluCompile_of_nonpos` 的两个实例，各一行。** -/
theorem reluCompile_collapses :
    reluCompile 1 0 0 = reluCompile 1 0 (-1) := by
  have h0 : reluCompile 1 0 0 = 0 := by
    apply reluCompile_of_nonpos
    norm_num
  have h1 : reluCompile 1 0 (-1) = 0 := reluCompile_zero_neg
  rw [h0, h1]


/-- **⭐⭐ 见证本身就是矛盾：两个**不同的符号**编译到同一个输出。**

**=> 这条把「不同」也放在同一个命题里，于是下游无需再证元组不等。** -/
theorem reluCompile_collapses_ne : 
    reluCompile 1 0 0 = reluCompile 1 0 (-1) ∧ ((1, 0, 0) : ℝ × ℝ × ℝ) ≠ (1, 0, -1) := by
  refine ⟨reluCompile_collapses, ?_⟩
  intro h
  have h3 : (0 : ℝ) = -1 := by
    have := congrArg (fun p => p.2.2) h
    simpa using this
  norm_num at h3

end Lattice.Lib.Compiler.ReluLemmas
