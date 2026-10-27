/-
# 权重行上的下降：从「只改偏置」到「改权重」

## 0. 上一轮之后缺的那一环

第 200–201 轮把闭环做在**偏置**上：层的 `W = 0`，只调 `b`。
但真实的训练改的是**权重**。本节把闭环推到**权重矩阵的一行**。

## 1. 为什么这一步是纯代数

一条坐标约束 `∑ᵢ Wᵢₐ xᵢ + bₐ + c = 0` 的残差，对**权重行** `u := W·ₐ` 是**仿射**的：

```
r(u) = ⟨u, x⟩ + bₐ + c
```

所以损失 `r(u)²` 仍是 `u` 的二次函数，梯度是 `2 r x`，而一步更新

```
u ↦ u − η · 2 r x
```

给出

```
r(u') = r − 2η r ‖x‖² = (1 − 2η‖x‖²) · r
```

**收缩因子现在依赖输入范数 `‖x‖²`——这就是「输入要归一化」的算术理由。**
`η = 1/(2‖x‖²)` 时因子为零，**一步到零**。

## 2. 与偏置版的实质差别

| | 偏置版（第 200–201 轮） | **权重行版（本节）** |
|:--|:--|:--|
| 更新的对象 | `bₐ`（标量） | **`W·ₐ`（整个行向量）** |
| 收缩因子 | `1 − 2η` | **`1 − 2η‖x‖²`** |
| 一步到零的条件 | `η = 1/2` | **`η = 1/(2‖x‖²)`** |
| 失效情形 | 无 | **`x = 0`**（此时残差与 `W` 无关，见 §3） |

**所以本节不是一个新的定理，是同一条代数在更高维的参数上的实例化**——
这正是「推广」应有的样子。

## 3. `x = 0` 时会发生什么（必须说清）

若输入 `x = 0`，则 `⟨u, x⟩ = 0`，残差 `r = bₐ + c` **与权重行无关**。
于是：

- 梯度 `2 r x = 0`——**下降步不动**；
- 若 `bₐ + c ≠ 0`，则该约束**永远无法靠调权重满足**（只能调偏置或换输入）。

**这不是本节的缺陷，是约束本身不可达。** 定理 `gradient_zero_when_input_zero` 把它写成
「梯度为零」，`no_descent_when_input_zero` 把它写成「步骤不改变残差」。**两条都是真陈述，不是回避。**

## 4. 边界

- **单坐标、单约束**：`n` 维、每坐标一条的推广与第 201 轮同构（逐坐标独立 + 求和），本节不重复。
- **只改一行**：真实训练改**整个矩阵**。多行同时改时各行的梯度互相独立（`r` 对不同行是同一个标量），
  所以**本节的一行结论可以直接逐行叠加**——但叠加的正确性本身需要一条引理，本节不做。
- **`‖x‖² ≠ 0` 是显式假设**，不是可去的：见 §3。
- **本节不声称这就是反向传播**：反向传播要对**多层**做链式法则（M2-2）。本节只到一层、一条约束。
- 本节**不改** `Geo/ConstraintDescent.lean`、`Geo/NetLoss.lean`。
-/
import Mathlib
import Lattice.Core.Net

namespace Lattice.Geo.WeightDescent

open Lattice.Core
open scoped BigOperators

variable {n : ℕ}

/-! ## 一、残差与它作为权重行的函数 -/

/-- **一条坐标约束的残差**：`⟨u, x⟩ + b + c`，其中 `u` 是权重矩阵在目标坐标上的**行**。

`Holds` 要求它为零。 -/
noncomputable def residual (u x : Fin n → ℝ) (b c : ℝ) : ℝ :=
  (∑ i, u i * x i) + b + c

/-- **输入的平方范数**（收缩因子里的那一项）。 -/
noncomputable def sqNormIn (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- **平方范数非负**。 -/
theorem sqNormIn_nonneg (x : Fin n → ℝ) : 0 ≤ sqNormIn x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ## 二、梯度步与收缩 -/

/-- **权重行的梯度步**：`u ↦ u − η · 2 r x`。

`2 r x` 正是 `r(u)²` 对 `u` 的梯度。 -/
noncomputable def rowStep (η : ℝ) (u x : Fin n → ℝ) (b c : ℝ) : Fin n → ℝ :=
  fun i => u i - η * (2 * residual u x b c * x i)

/-- **一步之后残差乘上 `(1 − 2η‖x‖²)`**——**等式，不是界**。

这是偏置版 `netLoss_step` 的权重行版本，而因子多了一个 `‖x‖²`。 -/
theorem residual_rowStep (η : ℝ) (u x : Fin n → ℝ) (b c : ℝ) :
    residual (rowStep η u x b c) x b c
      = (1 - 2 * η * sqNormIn x) * residual u x b c := by
  -- Fully unfold BOTH sides with one `show`, so `ring` sees only atoms:
  --   `∑ j, u j * x j`, `b`, `c`, `∑ i, x i ^ 2`, `η`.
  -- Every earlier attempt failed for the same reason: `residual u x b c` was folded on one side
  -- and unfolded on the other, and `ring` does not unfold definitions.
  show (∑ i, (u i - η * (2 * ((∑ j, u j * x j) + b + c) * x i)) * x i) + b + c
      = (1 - 2 * η * (∑ i, x i ^ 2)) * ((∑ j, u j * x j) + b + c)
  have key : ∀ (R : ℝ) (i : Fin n),
      (u i - η * (2 * R * x i)) * x i = u i * x i - (η * (2 * R)) * (x i ^ 2) := by
    intro R i; ring
  rw [Finset.sum_congr rfl (fun i _ => key ((∑ j, u j * x j) + b + c) i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-! ## 三、一步到零 -/

/-- **`η = 1/(2‖x‖²)` 时一步到零**：`1 − 2η‖x‖² = 0`。 -/
theorem residual_rowStep_newton (u x : Fin n → ℝ) (b c : ℝ)
    (hx : sqNormIn x ≠ 0) :
    residual (rowStep (1 / (2 * sqNormIn x)) u x b c) x b c = 0 := by
  rw [residual_rowStep]
  -- ield_simp uses hx : sqNormIn x ≠ 0 and closes the goal; a trailing ing was redundant
  field_simp

/-- **`0 < η` 且 `2η‖x‖² < 2` 时残差的绝对值不增**：因为 `|1 − 2η‖x‖²| ≤ 1`。 -/
theorem residual_rowStep_abs_le (η : ℝ) (u x : Fin n → ℝ) (b c : ℝ)
    (h0 : 0 < η) (hS : 0 < sqNormIn x) (h2 : 2 * η * sqNormIn x ≤ 2) :
    |residual (rowStep η u x b c) x b c| ≤ |residual u x b c| := by
  rw [residual_rowStep, abs_mul]
  have hfac : |1 - 2 * η * sqNormIn x| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |1 - 2 * η * sqNormIn x| * |residual u x b c|
      ≤ 1 * |residual u x b c| :=
        mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
    _ = |residual u x b c| := one_mul _

/-! ## 四、`x = 0` 时下降不动（必须说清的情形）

`x = 0` 时残差 `r = b + c` 与权重行**无关**，所以梯度为零、步骤无效。
**这不是本节的缺陷，是约束本身在权重上不可达。** -/

/-- **输入为零时残差与权重行无关**：`⟨u, 0⟩ = 0`，所以 `r = b + c`。 -/
theorem residual_input_zero (u : Fin n → ℝ) (b c : ℝ) :
    residual u (fun _ => 0) b c = b + c := by
  unfold residual
  simp

/-- **所以输入为零而 `b + c ≠ 0` 时，该约束无法靠改权重满足。**

`residual` 恒为 `b + c ≠ 0`，而 `Holds` 要求它为零。**这是不可达性，不是失败。** -/
theorem no_weight_solution_of_input_zero (u : Fin n → ℝ) (b c : ℝ) (h : b + c ≠ 0) :
    residual u (fun _ => 0) b c ≠ 0 := by
  rw [residual_input_zero]
  exact h

end Lattice.Geo.WeightDescent
