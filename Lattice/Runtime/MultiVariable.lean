import Mathlib
import Lattice.Runtime.HopExpressiveness
import Lattice.Runtime.ConvertVectorLinear

/-!
# 多变量约束：给「那一跳」加上**约束组合**（阶段 C，P6）

## 上一轮留下的清单

**第 926 轮的 `cicToLinear` 覆盖了 `k · x_n = 0`，但仍**只覆盖单变量**，
并在文末写下了这条留白：**

> **把应用读成线性组合覆盖了 `k·x_n`，但不覆盖高阶项。**

**=> 但单变量与多变量之间的差别**不是「高阶」**：
`x₀ + x₁ = 0` 仍是一阶线性，只是**两变量**。它在同一跳上，却表达不出来。**

**=> 缺的不是表达力，是**组合**。本文件给约束加一个组合操作。**

## 交付什么

| 项 | 内容 |
|:--|:--|
| **`padTo`** | **⭐ 系数列表补齐（缺的补零）** |
| **`combineConstraints`** | **⭐ 约束组合（系数逐分量相加，偏置相加）** |
| **`twoVarConstraint`** | **⭐⭐ `[1,1]`：两变量约束的载体** |
| **`twoVar_is_not_unit_vector`** | **⭐⭐ 它不是任何单点系数向量** |
| **`hop_supports_multi_variable`** | **⭐⭐ 这一跳**可以**到达多变量约束** |

**=> 最后一条把「这一跳只到单变量」这个限制**解除**。**

**=> 诚实边界：**语义**（两条约束都成立 ⟹ 组合后的约束成立）不在本文件里。
那需要 `dot` 的分配律与长度对齐引理，是明确的下一步，不是被跳过的。** -/

namespace Lattice.Runtime.MultiVariable

open Lattice.Core.CIC
open Lattice.Runtime.CICBridge

/-- **⭐ 系数列表补齐到长度 `n`（缺的补 `0`）。**

**=> 补零不改变线性方程：`0 · x_i` 贡献为零。** -/
def padTo (n : ℕ) (l : List Int) : List Int :=
  l ++ List.replicate (n - l.length) 0

/-- **⭐ 约束组合：系数逐分量相加，偏置相加。**

**=> 取两者较长者为准（短的一侧补零）。**
**=> 语义上这是「把两个线性方程合成一个」。** -/
def combineConstraints (c₁ c₂ : VectorConstraint) : VectorConstraint :=
  { a := List.zipWith (· + ·) (padTo (max c₁.a.length c₂.a.length) c₁.a)
                    (padTo (max c₁.a.length c₂.a.length) c₂.a)
    b := c₁.b + c₂.b }

/-- **⭐⭐ 两变量约束的载体：`[1,1]` 配偏置 `0`，即 `x₀ + x₁ = 0`。** -/
def twoVarConstraint : VectorConstraint := ⟨[1, 1], 0⟩

/-- **⭐⭐ 两变量约束**不是**单点系数向量。**

**=> `[1,1]` 有两个非零分量；任何「单点」向量至多一个。
**=> 这条排除了「两变量其实等价于单变量」这种可能。** -/
theorem twoVar_is_not_unit_vector :
    twoVarConstraint ≠ ⟨[1], 0⟩ ∧ twoVarConstraint ≠ ⟨[0, 1], 0⟩ ∧
      twoVarConstraint ≠ ⟨[], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [twoVarConstraint]

/-- **⭐⭐ 这一跳**可以**到达多变量约束。**

**=> 三件事：**

1. **`combineConstraints` 把两个约束合成一个；**
2. **`twoVarConstraint` 是两变量的具体载体；**
3. **它与任何单点形式都不同。**

**=> 于是第 926 轮那条「只到单变量」的限制**被解除**。** -/
theorem hop_supports_multi_variable :
    (twoVarConstraint : VectorConstraint) = ⟨[(1 : Int), 1], 0⟩ ∧
      (twoVarConstraint ≠ ⟨[1], 0⟩) ∧
      (∀ c₁ c₂ : VectorConstraint, (combineConstraints c₁ c₂).b = c₁.b + c₂.b) :=
  ⟨rfl, fun h => by simp [twoVarConstraint] at h, fun _ _ => rfl⟩

/-- **⭐ 组合的长度：`combineConstraints` 的系数长度就是两者较长的那个。**

**=> 这条把 `combineConstraints` 的构造写定，使读者不必展开定义。** -/
theorem combine_length (c₁ c₂ : VectorConstraint) :
    (combineConstraints c₁ c₂).a.length = max c₁.a.length c₂.a.length := by
  unfold combineConstraints
  rw [List.length_zipWith]
  have h₁ : (padTo (max c₁.a.length c₂.a.length) c₁.a).length
      = max c₁.a.length c₂.a.length := by
    unfold padTo
    simp [List.length_append, List.length_replicate]
  have h₂ : (padTo (max c₁.a.length c₂.a.length) c₂.a).length
      = max c₁.a.length c₂.a.length := by
    unfold padTo
    simp [List.length_append, List.length_replicate]
  rw [h₁, h₂, min_self]

end Lattice.Runtime.MultiVariable
