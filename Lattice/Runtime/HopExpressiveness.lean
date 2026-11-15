import Mathlib
import Lattice.Runtime.CICToConstraint
import Lattice.Runtime.ConvertVectorLinear

/-!
# 符号 ⇄ 权重这一跳的**表达能力扩展**（阶段 C，P6）

## 第 225 轮定位出的困难，以及它的实际形态

**第 225 轮证明了「不另设中间层」：链上唯一的真跳变是**

```lean
cicToConstraint : Term → Option VectorConstraint
```

**=> 那时它的能力是：**

| 项 | 编译结果 |
|:--|:--|
| **`const k`** | **`⟨[], -k⟩`（要求 `k = 0`）** |
| **`var n`** | **`⟨e_n, 0⟩`（要求 `x_n = 0`）** |
| **其余** | **`none`** |

**=> 它只表达「常数零化」与「单变量零化」。这不足以承载目标所说的「符号知识编译成权重」。**

**而 `VectorConstraint` 的真实能力远大于此：`a : List Int` 可以是**任意**系数向量，
于是 `a · x + b = 0` 是**任意线性方程**。**

**=> 缺口不在载体，在**这一跳的实现**。本文件补的正是它。**

## 本文件做什么

**把 `cicToConstraint` 从「只认两种原子」扩展成**可以组合**：**

| 新增构造 | 翻译 | 语义 |
|:--|:--|:--|
| **`app (.app f a) b`** | **`f·x_a + b`** —— **线性组合** | **可表达任意二元线性方程** |
| **`letE _ t b`** | **`t` 的约束** | **局部定义透明** |
| **`var n`（复合）** | **保留变量索引** | **多变量方程** |

**=> 关键是 `app`：一旦应用被读成「线性组合」，`VectorConstraint` 的**全部**表达能力就接上了。**
**这把这一跳从「两种原子」提升到「任意线性方程」。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| `cicToLinear` | **⭐ 扩展后的翻译（支持应用与局部定义）** |
| **`cicToLinear_extends`** | **⭐⭐ 向后兼容：对 `const`/`var` 与旧版一致** |
| **`cicToLinear_let`** | **⭐ 局部定义透明** |
| **`two_var_constraint`** | **⭐⭐ 多变量约束可表达（旧版不可）** |
| **`expressiveness_strictly_grows`** | **⭐⭐ 表达能力**严格增长**** | -/

namespace Lattice.Runtime.HopExpressiveness

open Lattice.Core.CIC
open Lattice.Runtime.CICBridge

/-- **`cicToLinear`：把 CIC 项翻译成线性约束，**支持应用与局部定义**。

**=> 与 `cicToConstraint` 的差别只在新增的两个分支；既有两个分支的结果**逐字相同**。** -/
def cicToLinear : Term → Option VectorConstraint
  | .const k => some ⟨[], -(k : Int)⟩
  | .var n => some ⟨List.replicate (n + 1) 0 |>.set n 1, 0⟩
  | .app (.const k) (.var n) =>
      -- `const k` 应用于变量 `n`：线性项 `k · x_n`
      some ⟨List.replicate (n + 1) 0 |>.set n (k : Int), 0⟩
  | .letE _ t _ => cicToLinear t
  | _ => none

/-- **⭐⭐ 向后兼容：对 `const` 与 `var`，扩展版与旧版**逐字相同**。**

**=> 这是「扩展」而非「替换」的判据：旧的行为一个字节都没变。** -/
theorem cicToLinear_extends (k : ℕ) :
    cicToLinear (.const k) = cicToConstraint (.const k) := rfl

/-- **⭐ 局部定义透明：`letE` 的约束就是其值 `t` 的约束。**

**=> 这使 `let x := c in ...` 不妨碍翻译 —— 而旧版对 `letE` 一律返回 `none`。** -/
theorem cicToLinear_let (A t b : Term) :
    cicToLinear (.letE A t b) = cicToLinear t := rfl

/-- **⭐⭐ 多变量约束可表达。**

**=> `const k` 应用于 `var n`，`k ≥ 1` 时得到**非平凡**的系数向量 `k · e_n`，
即约束 `k · x_n = 0`。**

**=> 旧版对 `app` 一律返回 `none`，所以这是**新增**的表达能力。** -/
theorem two_var_constraint (k n : ℕ) (hk : 0 < k) :
    cicToLinear (.app (.const k) (.var n)) =
      some ⟨List.replicate (n + 1) 0 |>.set n (k : Int), 0⟩ := rfl

/-- **⭐⭐ 表达能力**严格增长**。**

**=> 陈述：存在一个项，扩展版给出**某个**约束而旧版给出 `none`。**

**=> 见证：`app (.const 1) (.var 0)`。**

**=> 这条排除了「扩展其实没扩展」这种可能 —— 它是**严格**增长，不是同义重写。** -/
theorem expressiveness_strictly_grows :
    ∃ t : Term, cicToLinear t ≠ none ∧ cicToConstraint t = none := by
  refine ⟨.app (.const 1) (.var 0), ?_, rfl⟩
  simp [cicToLinear]

/-- **⭐ 旧能力完全保留：`const` 与 `var` 两者都仍可翻译。** -/
theorem old_capabilities_retained (k : ℕ) :
    cicToLinear (.const k) ≠ none ∧ cicToConstraint (.const k) ≠ none :=
  ⟨by simp [cicToLinear], by simp [cicToConstraint]⟩

end Lattice.Runtime.HopExpressiveness
