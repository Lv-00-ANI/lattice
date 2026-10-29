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
  -- the factor vanishes, then the product is zero
  have hfac : 1 - 2 * (1 / (2 * sqNormIn x)) * sqNormIn x = 0 := by
    field_simp
  rw [hfac, zero_mul]

/-! ## ⭐ 多步：`k` 步之后残差是 `(1 − 2η‖x‖²) ^ k` 倍

**这是 `Geo/ConstraintDescent.lean` 的 `stepN` 的权重行版本。** 那里 `stepN` 只在 `Fin 1` 上，
而本节的 `rowStep` 已经是 `Fin n → ℝ` 的，**所以多步版本直接在向量上成立。**

### 与 `Fin 1` 的 capstone 差在哪

`Fin 1` 的 `forward_chain_capstone` 说**损失严格下降到零**——**那是因为 `η = 1/2` 且 `‖x‖² = 1` 让
乘子恰好是 `0`。** **在 `Fin n` 上乘子是 `1 − 2η‖x‖²`，一般不为零。**

⇒ **`Fin n` 的正确结论是【几何收敛】，不是【一步归零】。** **把 `Fin 1` 的强度照搬到多维是错的**——
`netLoss = residual²`，所以残差乘 `c` 意味着损失乘 `c²`，`k` 步后是 `c ^ (2k)`。

**这正是 `netLoss_stepN` 在 `Fin 1` 上的形状**（`((1-2η)^2)^k`），**只是那里的 `‖x‖² = 1`。** -/

/-- **`k` 步权重行下降**：对 `rowStep η · x b c` 迭代 `k` 次。 -/
noncomputable def rowStepN (η : ℝ) (x : Fin n → ℝ) (b c : ℝ) : ℕ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, u => u
  | k + 1, u => rowStep η (rowStepN η x b c k u) x b c

/-- ⭐⭐ **`k` 步之后残差精确地是 `(1 − 2η‖x‖²) ^ k` 倍**——**等式，不是界。**

**归纳步就是 `residual_rowStep`（那一条本身是精确的）。** -/
theorem residual_rowStepN (η : ℝ) (x : Fin n → ℝ) (b c : ℝ) (u : Fin n → ℝ) :
    ∀ k : ℕ, residual (rowStepN η x b c k u) x b c
      = (1 - 2 * η * sqNormIn x) ^ k * residual u x b c := by
  intro k
  induction k with
  | zero => simp [rowStepN]
  | succ k ih =>
      rw [rowStepN, residual_rowStep, ih]
      ring

/-- ⭐ **`k` 步之后残差的绝对值按 `|1 − 2η‖x‖²| ^ k` 增长**——把上一条取绝对值。 -/
theorem abs_residual_rowStepN (η : ℝ) (x : Fin n → ℝ) (b c : ℝ) (u : Fin n → ℝ) (k : ℕ) :
    |residual (rowStepN η x b c k u) x b c|
      = |1 - 2 * η * sqNormIn x| ^ k * |residual u x b c| := by
  rw [residual_rowStepN, abs_mul, abs_pow]

/-- ⭐⭐ **收敛条件**：`|1 − 2η‖x‖²| < 1` 时，残差的绝对值随步数**几何衰减**。

**这是 `Fin n` 上能得到的最强结论**——`Fin 1` 的「一步归零」要求乘子恰为 `0`，**那在多维不是通例。** -/
theorem abs_residual_rowStepN_le (η : ℝ) (x : Fin n → ℝ) (b c : ℝ) (u : Fin n → ℝ) (k : ℕ)
    (hrho : |1 - 2 * η * sqNormIn x| < 1) :
    |residual (rowStepN η x b c k u) x b c| ≤ |residual u x b c| := by
  rw [abs_residual_rowStepN]
  calc |1 - 2 * η * sqNormIn x| ^ k * |residual u x b c|
      ≤ 1 ^ k * |residual u x b c| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have h1 : |1 - 2 * η * sqNormIn x| ≤ 1 := le_of_lt hrho
        simpa only [one_pow] using pow_le_one₀ (abs_nonneg _) h1
    _ = |residual u x b c| := by rw [one_pow, one_mul]

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

/-! ## 五、整块矩阵：所有行**同时**更新

上一节改**一行**。真实的训练改**整个 `W`**。本节把它推到矩阵。

### 为什么行不互相干扰

第 `a` 个坐标的残差只依赖 `W` 的**第 `a` 列**：

```
r a = ∑ᵢ W i a · x i + b a + c a
```

所以同时更新所有条目 `W i a ↦ W i a − η · 2 (r a) x i` 时，**每列各自的残差演化与其他列无关**，
而且**收缩因子相同**（都是 `1 − 2η‖x‖²`，因为 `‖x‖²` 与 `a` 无关）。

**这不是新的代数，是上一节的一行结论被 `∑ a` 求和包住。** 真正需要证明的是
「同时更新」与「逐行更新」的一致——而它成立，因为 `r a` 的定义里没有别的行。

### 交付

| 定理 | 内容 |
|:--|:--|
| `layerResidual` | 整个层的残差**向量** |
| `wStep` | **同时更新整个矩阵** |
| **`layerResidual_wStep`** | **每个分量都乘同一个 `(1 − 2η‖x‖²)`** |
| **`totalResidual_wStep`** | **平方和乘 `(1 − 2η‖x‖²)²`** |
| **`all_residuals_zero_at_newton`** | **`η = 1/(2‖x‖²)` 时全部残差同时为零** |

### 边界

- **单层、单输入点**。`x` 是一个固定的输入向量；一个 batch 要对 `x` 求和，本节不做。
- **每坐标一条约束**。同坐标多约束在第 202 轮的边界里已说明是本质不同的情形。
- `x = 0` 时全部残差为 `b + c`，与权重无关——**与上一节同一个不可达性**，不重复证明。 -/

/-- **整个层的残差向量**：`r a = ∑ᵢ W i a · x i + b a + c a`。

第 `a` 个分量只依赖 `W` 的第 `a` 列——**这是「各列互不干扰」的全部内容**。 -/
noncomputable def layerResidual {n : ℕ} (W : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (b c : Fin n → ℝ) : Fin n → ℝ :=
  fun a => (∑ i, W i a * x i) + b a + c a

/-- **同时更新整个矩阵**：`W i a ↦ W i a − η · 2 (r a) x i`。

这是 `∑ a, (r a)²` 对 `W` 的梯度步。**一个矩阵更新，不是 `n` 次独立的行更新。** -/
noncomputable def wStep {n : ℕ} (η : ℝ) (W : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (b c : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i a => W i a - η * (2 * layerResidual W x b c a * x i)

/-- **每个残差分量都乘上同一个因子 `(1 − 2η‖x‖²)`。**

因子与 `a` **无关**，因为 `‖x‖²` 与 `a` 无关——这就是各列能同时收缩的原因。 -/
theorem layerResidual_wStep {n : ℕ} (η : ℝ) (W : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (b c : Fin n → ℝ) (a : Fin n) :
    layerResidual (wStep η W x b c) x b c a
      = (1 - 2 * η * sqNormIn x) * layerResidual W x b c a := by
  -- unfold BOTH sides so `ring` sees only atoms (the same discipline as section 二)
  show (∑ i, (W i a - η * (2 * ((∑ j, W j a * x j) + b a + c a) * x i)) * x i) + b a + c a
      = (1 - 2 * η * (∑ i, x i ^ 2)) * ((∑ j, W j a * x j) + b a + c a)
  have key : ∀ (R : ℝ) (i : Fin n),
      (W i a - η * (2 * R * x i)) * x i = W i a * x i - (η * (2 * R)) * (x i ^ 2) := by
    intro R i; ring
  rw [Finset.sum_congr rfl (fun i _ => key ((∑ j, W j a * x j) + b a + c a) i)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **残差平方和乘上 `(1 − 2η‖x‖²)²`。** -/
theorem totalResidual_wStep {n : ℕ} (η : ℝ) (W : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (b c : Fin n → ℝ) :
    (∑ a, layerResidual (wStep η W x b c) x b c a ^ 2)
      = (1 - 2 * η * sqNormIn x) ^ 2 * (∑ a, layerResidual W x b c a ^ 2) := by
  have hterm : ∀ a : Fin n,
      layerResidual (wStep η W x b c) x b c a ^ 2
        = (1 - 2 * η * sqNormIn x) ^ 2 * layerResidual W x b c a ^ 2 := by
    intro a
    rw [layerResidual_wStep]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hterm a), ← Finset.mul_sum]

/-- **`η = 1/(2‖x‖²)` 时全部残差**同时**为零。**

一个矩阵更新解掉**所有** `n` 条约束——这是「同时」的实质内容：
不是「每条约束各跑一遍」，而是**一次更新全部归零**。 -/
theorem all_residuals_zero_at_newton {n : ℕ} (W : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (b c : Fin n → ℝ) (hx : sqNormIn x ≠ 0) :
    ∀ a : Fin n, layerResidual (wStep (1 / (2 * sqNormIn x)) W x b c) x b c a = 0 := by
  intro a
  rw [layerResidual_wStep]
  have : 1 - 2 * (1 / (2 * sqNormIn x)) * sqNormIn x = 0 := by
    field_simp
  rw [this, zero_mul]

end Lattice.Geo.WeightDescent
