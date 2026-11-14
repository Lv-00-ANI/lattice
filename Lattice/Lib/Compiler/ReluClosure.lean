import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Lib.Editing.RealNonlinearExtract
import Lattice.Lib.Compiler.Expressiveness

/-!
# relu 载体的闭环：非线性一侧也有「编译 ⇄ 提取 ⇄ 验证」（阶段 C，P6）

## 为什么需要这一份

**第 904 轮证明了线性载体覆盖的是**等式子类**，而 `relu` 侧表达的是**不等式**：**

```lean
theorem expressiveness_strictly_wider :
    (∀ a b x, a * x + b = 0 → a * x + b ≤ 0) ∧
    (∃ a b x, a * x + b ≤ 0 ∧ a * x + b ≠ 0)
```

**=> 那说明线性链**不够**表达力。但它没有说明 `relu` 侧**能否**承载闭环。**
**若不能，则「表达力更宽」只是一个关于单点的观察，而不是一条可用的链。**

**本文件把闭环搬到 `relu` 载体上。**

## 关键事实：`relu` 不是单射，因此「提取」不是逆

**`relu x = max x 0`：所有 `x ≤ 0` 都映到 `0`。**

**=> 所以 `relu` 侧**不存在**左逆 —— `reluInv x := x`（`RealNonlinearExtract.lean:70`）
**不能**满足 `reluInv (relu x) = x`。**

**这不是缺陷，而是**载体本身的性质**。于是 `relu` 侧的「提取」必须换一种读法：**

| 线性载体的提取 | relu 载体的提取 |
|:--|:--|
| **`extractVec (convertVec c) = c`（真逆）** | **不存在真逆** |
| **——** | **`relu` 保持的是**满足关系**，不是值** |

**=> 所以 relu 侧的闭环只能是**语义层**的：**

**「约束成立」⟺「编译后的输出为零」，而这两者的等价**本身就是**可验证的判据。**

**这正是 `reluCompile_preserves` 的内容。本文件把它组织成与线性侧对称的三件事。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `relu_not_injective` | **⚠ 否证：`relu` 不是单射，因此没有左逆** |
| `reluInv_not_left_inverse` | **⚠ 把上一条具体化到已有的 `reluInv`** |
| **`relu_verify_criterion`** | **⭐ 判据：约束成立 ⟺ 编译输出为零（与线性侧同形）** |
| **`relu_repair_preserves_sat`** | **⭐ 修正：满足的点被保持** |
| **`relu_solution_is_ray`** | **⭐ 解集是**射线**（这正是线性侧给不出的形状）** |

**最后一条是本轮的要点：`relu` 侧的解集是**无界射线**，而线性侧的解集是**仿射子空间**。
两者形状不同，正是表达力之差在解集上的显现。** -/

namespace Lattice.Lib.Compiler.ReluClosure

open Lattice
open Lattice.Lib.Compiler

/-- **⚠ `relu` 不是单射。**

**=> 见证：`relu 1 = 1 = relu 2` 不成立，但 `relu (-1) = 0 = relu (-2)`。
所以 `relu (-1) = relu (-2)` 而 `-1 ≠ -2`。**

**=> 这条**否证**了「relu 侧存在真逆」——它是 relu 载体与线性载体的**结构性差别**。** -/
theorem relu_not_injective : ¬ Function.Injective (fun x : ℝ => relu x) := by
  intro h
  have heq : relu (-1) = relu (-2) := by
    unfold relu; norm_num
  have := h heq
  norm_num at this

/-- **⚠ 已有的 `reluInv` **不是** `relu` 的左逆。**

**=> `reluInv (relu (-1)) = relu (-1) = 0 ≠ -1`。**

**=> 这说明 relu 载体的「提取」不能照搬线性侧的做法；
它必须是**语义**层面的（下一条），而不是值层面的。** -/
theorem reluInv_not_left_inverse :
    ¬ Function.LeftInverse reluInv (fun x : ℝ => relu x) := by
  intro h
  have := h (-1)
  unfold reluInv relu at this
  norm_num at this

/-- **⭐ relu 侧的**验证判据**：约束成立 ⟺ 编译输出为零。**

**=> 与线性侧的 `symbolToWeight_correct` **同形**：
两边都是「符号侧成立 ⟺ 权重侧输出为零」。**

**=> 差别在**约束的语义**（等式 vs 不等式），不在判据的形状。** -/
theorem relu_verify_criterion (a b : ℝ) (x : ℝ) :
    ReluConstrSat a b x ↔ reluCompile a b x = 0 :=
  reluCompile_preserves a b x

/-- **⭐ 修正的保持性：满足的点，编译输出为零，且**任何**满足的点的输出都为零。**

**=> 这是 relu 侧「不改动已满足的点」的形式：**
**`ReluConstrSat a b x` 一旦成立，`reluCompile a b x` 就恒为零 —— 修复步骤无事可做。** -/
theorem relu_repair_preserves_sat (a b x : ℝ) (h : ReluConstrSat a b x) :
    reluCompile a b x = 0 :=
  (relu_verify_criterion a b x).mp h

/-- **⭐ 解集的形状：一条**射线**。**

**=> 若 `a > 0`，则 `ReluConstrSat a b x ⟺ x ≤ -b/a`。
即解集是 `(-∞, -b/a]`，一条**无界射线**。**

**=> 对比线性侧：`VectorConstraintSat c x := dot c.a x + c.b = 0` 的解集是**仿射子空间**（仿射超平面）。
两者形状不同 —— 这就是第 904 轮「严格更宽」在解集上的显现。** -/
theorem relu_solution_is_ray (a b : ℝ) (ha : 0 < a) (x : ℝ) :
    ReluConstrSat a b x ↔ x ≤ -b / a := by
  unfold ReluConstrSat
  constructor
  · intro h
    have : a * x ≤ -b := by linarith
    exact (le_div_iff₀ ha).mpr (by nlinarith)
  · intro h
    have hx : x * a ≤ -b := (le_div_iff₀ ha).mp h
    nlinarith

/-- **⭐ 闭环在 relu 侧的最强形式：验证 + 修正合并。**

**=> 对任意 `a b x`：**（约束成立 ⟺ 输出为零）** 且 **（若约束成立则不需要修复）。**

**=> 这与线性侧的 `repair_preserves_verdict` 对应，但**前提更弱**：
线性侧需要 `Repair` 实例，这里只需 `relu` 的代数性质。** -/
theorem relu_closure (a b : ℝ) (x : ℝ) :
    (ReluConstrSat a b x ↔ reluCompile a b x = 0) ∧
    (ReluConstrSat a b x → reluCompile a b x = 0) :=
  ⟨relu_verify_criterion a b x, relu_repair_preserves_sat a b x⟩

end Lattice.Lib.Compiler.ReluClosure
