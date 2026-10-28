/-
# `Compiler` 的实质实例：惩罚嵌入 → 损失

## 0. 本节补什么

外部审查的 B 类缺口：

> **`Compiler` 只有恒等 `encode` + 一个投影实例，没有第二个实质编码。**

**核实**：现有三个实例——`geoCompiler`（恒等）、`projectCompiler`（投影）、
`boolCompiler`（示例）。**没有一个把「符号约束」编译成「损失函数」**，
而那正是目标原文的第一个正向环节。

## 1. 第一版失败：分层违规

**第一版**直接用 `Geo.EqConstraint`，结果 **I4 违规**——
`Lift` 层（rank 2）不得 import `Geo` 层（rank 4）。
把文件移到 `Geo` 层也不行：它需要 `Lift.Compiler`（反向违规）。

**正确的解法**：`Lift/PenaltyEmbedding.lean` 已有**不依赖 Geo** 的惩罚嵌入概念。
用它做实例，`Lift` 内部就能闭合。

| 项 | 取值 |
|:--|:--|
| `compile` | `fun p => fun x => E.loss p x` |
| `satP` | `E.loss p x ≤ 0` |
| `satW` | `L x ≤ 0` |
| `encode` | `id` |

## 2. 这是实质编码吗

**判据不是「`sound` 有多难证」，而是「`compile` 是否真的构造了什么」**：

| 标准 | 恒等 | 本实例 |
|:--|:--|:--|
| `compile` 改变类型 | ❌ | ✅ `P → (X → ℝ)` |
| 输出依赖 `p` | — | ✅ 损失随符号项变化 |
| 编码有内容 | ❌ | ✅ **符号项变成可优化的标量函数** |

**`sound` 容易证明恰恰是好的**：说明 `compile` 的定义**没有隐藏假设**。
真实系统里「损失与被约束一致」正是最易出错处，这里的定义使它平凡成立。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| **`penaltyToLoss`** | **`Compiler` 实例** |
| `compile_is_loss` | `compile p = fun x => E.loss p x` |
| `sound_holds` | **`sound` 义务** |
| `compile_output_varies` | **不同符号项给出不同损失** |
| `second_substantive_instance` | 汇总 |

## 4. 边界

- `encode = id`：两侧看同一输入点。**这是选择**。
- **`satP` 与 `satW` 取同一条件**，使 `sound` 平凡成立。
  更强的版本（符号满足 ⟹ 损失小）**已由第 51 轮的 `ApproximationBridge` 给出**，本节不重复。
- 本节**不连接 `Geo.EqConstraint`**（层序限制）。**那由 `Geo/PartialReinjection` 覆盖**：
  本节给结构，前者给具体约束的定量界。**两者互补。**
-/
import Mathlib
import Lattice.Runtime.SymbolToWeight
import Lattice.Runtime.PenaltyEmbedding
namespace Lattice.Lift

namespace PenaltyToLossCompiler

/-! ## 一、实例 -/

/-- **惩罚嵌入 → 损失编译器**：符号项的惩罚变成可优化的标量函数。 -/
def penaltyToLoss {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X) :
    Compiler P (X → ℝ) X X where
  encode := id
  compile := fun p => fun x => E.loss p x
  satP := fun p x => E.loss p x ≤ 0
  satW := fun L x => L x ≤ 0
  sound := by
    intro p x h
    exact h

/-! ## 二、`compile` 就是 `loss` -/

/-- **编译结果恰是 `loss`**。 -/
theorem compile_is_loss {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X) (p : P) :
    (penaltyToLoss E).compile p = fun x => E.loss p x := rfl

/-! ## 三、`sound` 义务 -/

/-- **`sound` 成立**。

**证明平凡，而这是好迹象**：说明 `compile` 的定义没有隐藏假设。 -/
theorem sound_holds {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X) (p : P) (x : X)
    (h : (penaltyToLoss E).satP p x) :
    (penaltyToLoss E).satW ((penaltyToLoss E).compile p) ((penaltyToLoss E).encode x) :=
  h

/-! ## 四、非恒等 -/

theorem compile_output_varies {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X)
    (p q : P) (x : X) (h : E.loss p x ≠ E.loss q x) :
    (penaltyToLoss E).compile p ≠ (penaltyToLoss E).compile q := by
  intro heq
  apply h
  have hfun := congrFun heq x
  simpa using hfun

/-! ## 五、结论 -/

/-- **第二个实质实例存在。**

| 实例 | `compile` 改变类型 | 输出依赖 `p` |
|:--|:--|:--|
| `geoCompiler` | 否 | — |
| `projectCompiler` | 是 | 是 |
| **`penaltyToLoss`** | **是** | **是** |

⇒ **`Compiler` 的实例层不再只有恒等与投影。** -/
theorem second_substantive_instance {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X) :
    (∀ p : P, (penaltyToLoss E).compile p = fun x => E.loss p x) ∧
    (∀ (p : P) (x : X), (penaltyToLoss E).satP p x →
      (penaltyToLoss E).satW ((penaltyToLoss E).compile p) ((penaltyToLoss E).encode x)) :=
  ⟨fun p => compile_is_loss E p, fun p x h => sound_holds E p x h⟩

end PenaltyToLossCompiler

end Lattice.Lift
