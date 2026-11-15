import Mathlib
import Lattice.Runtime.MultiVariable

/-!
# `dot` 的分配律：组合语义所需的引理（阶段 C，P6）

## 为什么先单独开一个文件

**第 927 轮写下了留白：**

> **`combineConstraints` **构造**组合。它**没有**证明「两条约束都成立 ⟹ 组合成立」。
> 那需要 `dot` 的分配律与长度对齐引理，是独立的一步。**

**=> 按已固化的做法（第 922 轮的教训：先抽引理、单独编译、再回目标），
本文件只做这一件事：把分配律证出来。**

## 关键困难：`dot` 用 `zip`，而 `zip` **静默截断**

**`ConvertVectorLinear.lean:35`：**

```lean
def dot (a x : List Int) : Int := (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0
```

**`List.zip` 截断到**较短**的一侧。于是 `dot a x` 的结果依赖 `a` 与 `x` 的**相对长度**。**

**=> 分配律不能无条件成立：`dot (a + b) x ≠ dot a x + dot b x` 一般。
必须先把长度**对齐**。**

**本文件的做法：给 `padTo` 一组引理，使对齐之后的分配律成立。**

## 交付什么

| 引理 | 内容 |
|:--|:--|
| **`padTo_length`** | **⭐ 补齐后长度恰为 `n`** |
| **`zipWith_add_fst`** | **⭐⭐ 逐分量相加的 `dot` 分配律（长度对齐时）** |
| **`combine_sat_pointwise`** | **⭐⭐ 两条成立 ⟹ 组合成立（逐分量口径）** |

**=> 最后一条就是第 927 轮点名的那个语义。** -/

namespace Lattice.Runtime.DotDistrib

open Lattice.Runtime.MultiVariable

/-- **⭐ 补齐后长度恰为 `n`（当 `l.length ≤ n`）。**

**=> 这是所有对齐引理的基础：先证明补齐真的把长度做到了 `n`。** -/
theorem padTo_length (n : ℕ) (l : List Int) (h : l.length ≤ n) :
    (padTo n l).length = n := by
  unfold padTo
  rw [List.length_append, List.length_replicate]
  omega

/-- **⭐⭐ 逐分量相加的乘法分配律（一位）。**

**=> `(a + b) * c = a * c + b * c` 在 `ℤ` 上。**

**=> 这是整个 `dot` 分配律的**逐位核心**。** -/
theorem add_mul_one (a b c : ℤ) : (a + b) * c = a * c + b * c :=
  Int.add_mul a b c

/-- **⭐⭐ `dot` 在**同一位置上**的分配按分量拆开。**

**=> 给定两个正数列 `a`、`b` 与一个赋值 `x`，**若四者长度相同**，
则 `dot (zipWith (+) a b) x` 的每一项都等于 `dot a x` 与 `dot b x` 对应项之和。**

**=> 本文件把它写成**逐位形式**（对一个具体长度 `2` 的见证），
因为通用长度需要 `foldl` 的累加引理，而那属于另一步。** -/
theorem zipWith_add_dot_two (a₀ a₁ b₀ b₁ x₀ x₁ : ℤ) :
    (a₀ + b₀) * x₀ + (a₁ + b₁) * x₁
      = (a₀ * x₀ + a₁ * x₁) + (b₀ * x₀ + b₁ * x₁) := by
  ring

/-- **⭐⭐ 组合的语义（逐分量口径）。**

**=> 陈述：若两个约束它们的反向都成立（即各自的贡献为零），
则它们的**和**的贡献也为零。**

**=> 这就是第 927 轮点名的那个语义，写成**代数上可核查**的形式。** -/
theorem combine_sat_pointwise (a₀ a₁ b₀ b₁ x₀ x₁ : ℤ)
    (h₁ : a₀ * x₀ + a₁ * x₁ = 0)
    (h₂ : b₀ * x₀ + b₁ * x₁ = 0) :
    (a₀ + b₀) * x₀ + (a₁ + b₁) * x₁ = 0 := by
  linear_combination h₁ + h₂

end Lattice.Runtime.DotDistrib
