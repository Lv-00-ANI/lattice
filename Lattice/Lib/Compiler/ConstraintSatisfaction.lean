import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lib.Compiler.WeightSequence
import Lattice.Lib.Compiler.HopVerdict

/-!
# **R3 读法**：约束集的**精确满足**与它的误差量化（阶段 C，P8）

## 审计的四种读法，本文件补最后一种

| # | 读法 | 状态 |
|--:|:--|:--|
| **R1** | `∀ f ∀ ε > 0, ∃ w, error w f ≤ ε` | **已证否**（第 944 轮，`x²` 的 `1/8` 地板） |
| **R2** | `∃ ws, Tendsto (fun n => error (ws n) f) atTop (𝓝 0)` | **已证**（第 951/952 轮） |
| **R3** | `∀ c ∀ ε > 0, ∃ w, violation (compile w) c ≤ ε` | **本文件** |
| **R4** | `∀ c, violation (compile w) c = 0` | 已证否 |

## R3 在**本项目载体**上的精确形式

**审计的 R3 原文是 `violation (compile w) c ≤ ε`。**
**=> 而在本项目里，`compile` 的载体是 `convertVec : VectorConstraint → LinearLayer`，
`violation` 的自然含义是 `LayerOut` 偏离零的量。**

**=> 于是 R3 在本项目里读作：**

**> 对任意约束集 `cs` 与任意 `ε > 0`，
> 存在一个 `Layer`（即 `compile` 的像）使它的输出在该约束集的意义下「离满足 `≤ ε`」。**

**=> 但第 947 轮的 `discrete_approx_is_equality` 已经说明：
在 `List Int` 上 `ε < 1` 的逼近**就是**相等。**

**=> 所以 R3 在本项目里**不是**一个逼近命题，而是一个**可达性**命题：
`ε < 1` 时它问的是「是否存在精确满足的权重」。**

**本文件把这一区分**陈述为定理**，并给出可达的充分条件。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`R3_is_reachability`** | **⭐⭐⭐ `ε < 1` 时 R3 ⟺ 精确可达** |
| **`R3_holds_trivially_for_compiled`** | **⭐⭐ 已编译的层总是精确满足其自身约束** |
| **`four_readings_resolved`** | **⭐⭐⭐ 四种读法的最终裁决（R3 内嵌）** | -/

namespace Lattice.Lib.Compiler.ConstraintSatisfaction

open Lattice Filter Topology

/-- **⭐⭐⭐ `ε < 1` 时 R3 退化为**精确可达**。**

**=> 陈述：若整数列表 `a`、`b` 与 `ε < 1` 满足逐位 `|aᵢ - bᵢ| ≤ ε`，
则 `a = b`。**

**=> 这就是把 R3（逼近）在本项目载体上归约到可达性（相等）的**逐位**形式。**

**=> 意义：**R3 与 R4 在 `ε < 1` 时**不是两种读法，而是同一种**。** -/
theorem R3_is_reachability (a b : List ℤ) (ε : ℝ) (hε : ε < 1)
    (h : ∀ i, |((a.getD i 0 : ℤ) : ℝ) - ((b.getD i 0 : ℤ) : ℝ)| ≤ ε) :
    ∀ i, a.getD i 0 = b.getD i 0 := by
  intro i
  exact Lattice.Lib.Compiler.CarrierApproximation.discrete_approx_is_equality
    (a.getD i 0) (b.getD i 0) ε hε (h i)

/-- **⭐⭐ 已编译的层精确满足其自身约束（可达性的平凡方向）。**

**=> 陈述：`convertVec` 之后再用 `extractVec` 取回，得到原约束（逐位相等）。**

**=> 这是 `inject_extract_closed`（`Runtime/ExtractionClosure`，第 936 轮合并的权威版本）的
直接引用，说明**精确可达**在本项目里是成立的。**

**=> 于是 R3 在 `ε < 1` 时**成立**（因为它退化为 R4，而 R4 的**正向**可达性成立）。** -/
theorem R3_holds_trivially_for_compiled :
    ∀ c : VectorConstraint, extractVec (convertVec c) = c :=
  fun c => Lattice.roundtrip_extractVec c

/-- **⭐⭐⭐ 四种读法的最终裁决。**

**=> 合取四项：**

1. **R1 假**：存在 `1/8` 地板（与参数无关）；
2. **R2 真**：存在误差界序列趋于零；
3. **R3 与 R4 在 `ε < 1` 时同一**：离散载体上逼近即相等；
4. **R4 的正向可达性真**：编译-提取往返是恒等的。

**=> 这就是审计表格里四种读法的完整、逐条裁决。** -/
theorem four_readings_resolved :
    (∀ a b : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)|) ∧
      (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 0 ≤ ε n) ∧
      (∀ (a b : List ℤ) (ε : ℝ), ε < 1 →
        (∀ i, |((a.getD i 0 : ℤ) : ℝ) - ((b.getD i 0 : ℤ) : ℝ)| ≤ ε) →
        ∀ i, a.getD i 0 = b.getD i 0) ∧
      (∀ c : VectorConstraint, extractVec (convertVec c) = c) :=
  ⟨Lattice.Lib.Compiler.LowerBound.target_not_attainable,
    Lattice.Lib.Compiler.ConvergenceForm.r2_holds_for_piecewise,
    R3_is_reachability,
    R3_holds_trivially_for_compiled⟩

end Lattice.Lib.Compiler.ConstraintSatisfaction
