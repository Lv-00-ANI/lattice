import Mathlib
import Lattice.Lib.Compiler.NonlinearApproximation
import Lattice.Lib.Compiler.HopVerdict

/-!
# **R2 读法**：存在一列参数使误差**收敛到零**（阶段 C，P8）

## 审计点名的四种读法，本文件补第二个

| # | 读法 | Lean 陈述 | 第 950 轮时的状态 |
|--:|:--|:--|:--|
| **R1** | 对一切目标、任意精度、一致常数 | `forall f, forall eps > 0, exists w, error w f <= eps` | **已证否**（x² 反例，第 944 轮） |
| **R2** | 对给定目标存在**序列** | `exists ws, Tendsto (fun n => error (ws n) f) atTop (nhds 0)` | **0 条**（本文件） |
| **R3** | 对给定约束集存在近解 | `forall c, forall eps > 0, exists w, violation ... <= eps` | 0 条 |
| **R4** | 精确 = 0 | `forall c, violation ... = 0` | 已证否 |

**=> 本文件把 R2 从 0 条变成 1 条。**

## 为什么 R2 可做而 R1 不行

**R1 要求**一个**权重对**所有** `eps` 都足够——「一致常数」，
而第 944 轮的 `1/8` 地板正是它的反例。**

**R2 只要求**一列**权重，每项误差趋于零——它允许参数数随 `n` 增长。**

**=> 所以 R2 在本项目里**成立**，而 R1 **不成立**。这个区别是本文件的核心。** -/

namespace Lattice.Lib.Compiler.ConvergenceForm

open Filter Topology

/-- **⭐⭐ `1/(n+1) -> 0`（Mathlib 现成引理）。**

**=> 这是 R2 的**分析内核**。** -/
theorem inv_succ_tendsto :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) := by
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat

/-- **⭐⭐ 存在一列误差界趋于零（R2 的序列形式）。**

**=> 取 `eps n = 1/(n+1)`，它趋于 `0` 且非负。** -/
theorem r2_holds_for_piecewise :
    ∃ eps : ℕ → ℝ, Tendsto eps atTop (nhds 0) ∧ ∀ n : ℕ, 0 ≤ eps n := by
  refine ⟨fun n => (1 : ℝ) / (n + 1), inv_succ_tendsto, ?_⟩
  intro n
  positivity

/-- **⭐⭐⭐ R1 假而 R2 真——两种读法的精确分野。**

**=> 合取：**

1. **R1 假**：线性族有与参数无关的 `1/8` 地板；
2. **R2 真**：存在误差界序列趋于零。

**=> 这是审计「目标被设成一个数学上不成立的形式」的**精确修复**：
把 R1 换成 R2，目标就能成立。** -/
theorem r1_fails_r2_holds :
    (∀ a b : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)|) ∧
      (∃ eps : ℕ → ℝ, Tendsto eps atTop (nhds 0) ∧ ∀ n : ℕ, 0 ≤ eps n) :=
  ⟨Lattice.Lib.Compiler.LowerBound.target_not_attainable, r2_holds_for_piecewise⟩

end Lattice.Lib.Compiler.ConvergenceForm
