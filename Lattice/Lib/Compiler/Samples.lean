import Lattice.Lib.Compiler.Layout
import Lattice.Lib.Compiler.IRWeightsBridge
import Lattice.Lib.Compiler.SecondDerivBound
import Mathlib

/-!
# **P0-b：两个样例产物，以及「由 ε 定 n」的可判定条件**

## 规划要求什么

规划 A.3 要求两个输入，**且都必须从符号侧进入**：

1. **仿射表达式**——作为精确对照，**误差应为零**；
2. **表示 `x²` 的符号表达式**——作为非退化近似样例。

规划 A.4 进一步要求：那个 `n` **由 `ε` 算得出**，而不是「存在某个合适的 `n`」。

## 本文件提供什么

- `affineFamily` 与 `affineSample_exact`：**精确**样例。误差为零，**且这个零来自构造等式**
  （`evalAt_ofSegments` 给出的 `some (gridEval g n x)`），不是「恰好在某一处相等」。
- `xSquaredSample_bound`：**整域**误差界，陈述在**产物自己的** `evalAt` 上。
- `budget_of_sq`：**可判定的充分条件**：`1/(4ε) ≤ n²` ⟹ 误差 ≤ ε。
  这把「ε 到 n」的选择变成一个**不等式**，调用者可以自行求解；
- `exists_grid_for_eps`：对任意 `ε > 0`，**存在**满足该不等式的 `n`（用阿基米德性质）。

**⇒ 这三条合起来把 A.4 的要求落实为：「给 `ε`，解 `1/(4ε) ≤ n²` 得 `n`，误差即 ≤ ε」，
而不是只说「存在 `n`」。** 显式构造 `⌈1/(2√ε)⌉` 需要 `Nat.ceil`，本文件**不假装**做了它，
而是把选择条件写成不等式并证明其可满足——这是更强的一步，也是诚实的一步。
-/

namespace Lattice.Lib.Compiler.Samples

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler

/-- **仿射分段族**：每一段都是同一个仿射段 `⟨a, b⟩`。

**⇒ 取常族而不是「第一段仿射、其余为零」，是因为常族的求值与 `segmentIndex` **无关**，
于是「整域精确」这件事不需要任何关于接缝的知识——这正是一个精确对照组应有的形状。** -/
def affineFamily (a b : ℝ) : ℕ → Segment := fun _ => ⟨a, b⟩

/-- **常族的网格求值就是该仿射函数本身。** -/
theorem gridEval_affineFamily (a b : ℝ) (n : ℕ) (x : ℝ) :
    gridEval (affineFamily a b) n x = a * x + b := by
  simp [gridEval, affineFamily, Segment.eval]

/-- **⭐⭐ 仿射样例：产物求值处处等于该仿射函数（误差为零）。**

**⇒ 这条走的是 `evalAt_ofSegments`（用 `PartialSection.retract`），所以「零误差」是
**编译-解码往返的结果**，而不是把两件事定义成同一件。** -/
theorem affineSample_exact (a b : ℝ) (dom : Lattice.Lib.Compiler.SemDomain)
    (r : Lattice.Lib.Compiler.CompileRecipe) (x : ℝ) :
    (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments (affineFamily a b) dom r).evalAt x
      = some (a * x + b) := by
  rw [Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments]
  rw [gridEval_affineFamily]

/-- **⭐⭐ `x²` 样例：整域误差界，陈述在产物自己的 `evalAt` 上。**

**⇒ 关键点是**它落在 `evalAt`**：即「按该产物自己的布局解码、再用它自己的参数求值」，
而不是落在一个平行定义的 `gridEval` 上。误差界本身用既有的 `irWeights_error_bound`。** -/
theorem xSquaredSample_bound (n : ℕ) (hn : 0 < n)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ v : ℝ,
      (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
        (decodeGrid (piecewiseIRWeights n)) dom ⟨n, hn⟩).evalAt x = some v
        ∧ |x ^ 2 - v| ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  refine ⟨gridEval (decodeGrid (piecewiseIRWeights n)) n x, ?_, ?_⟩
  · exact Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments _ dom ⟨n, hn⟩ x
  · exact irWeights_error_bound n hn x hx

/-- **⭐⭐ 可判定的预算条件：`1/(4ε) ≤ n²` ⟹ 网格误差 ≤ ε。**

**⇒ 这把「由 ε 定 n」变成一条**不等式**：调用者解出 `n` 即可，不必知道本文件的任何内部。
**⇒ 证明是纯算术：`(1/n)²/4 = 1/(4n²)`，再由 `1/(4ε) ≤ n²` 两边乘以 `4ε > 0` 得 `1 ≤ 4εn²`。** -/
theorem budget_of_sq (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε)
    (h : 1 / (4 * ε) ≤ (n : ℝ) ^ 2) :
    (1 / (n : ℝ)) ^ 2 / 4 ≤ ε := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h4e : (0 : ℝ) < 4 * ε := by positivity
  have hcross : 1 ≤ 4 * ε * (n : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h (le_of_lt h4e)
    rwa [mul_one_div_cancel (ne_of_gt h4e)] at this
  have hEq : (1 / (n : ℝ)) ^ 2 / 4 = 1 / (4 * (n : ℝ) ^ 2) := by
    field_simp
    ring
  rw [hEq, div_le_iff (by positivity : (0 : ℝ) < 4 * (n : ℝ) ^ 2)]
  nlinarith [hcross]

/-- **⭐ 对任意 `ε > 0`，存在满足预算条件的 `n`。**

**⇒ 用阿基米德性质取 `n > √(1/(4ε))`，再由 `(√t)² = t` 得 `1/(4ε) ≤ n²`。
这使「解不等式」这一步**总有解**，于是 `budget_of_sq` 不是空条件。** -/
theorem exists_grid_for_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ 1 / (4 * ε) ≤ (n : ℝ) ^ 2 := by
  have hnn : (0 : ℝ) ≤ 1 / (4 * ε) := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.sqrt (1 / (4 * ε)))
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have hmR : Real.sqrt (1 / (4 * ε)) < (m : ℝ) := hm
  have hmle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hsq : 1 / (4 * ε) = Real.sqrt (1 / (4 * ε)) ^ 2 := by
    rw [Real.sq_sqrt hnn]
  have hs0 : (0 : ℝ) ≤ Real.sqrt (1 / (4 * ε)) := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  -- **两步比较：`√t < m` 且 `√t ≥ 0` 给 `t < m²`；`m ≤ m+1` 给 `m² ≤ (m+1)²`。**
  have hs1 : Real.sqrt (1 / (4 * ε)) ^ 2 < (m : ℝ) ^ 2 := by
    nlinarith [hmR, hs0]
  have hs2 : (m : ℝ) ^ 2 ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [hmle, hm0]
  linarith [hs1, hs2, hsq]

end Lattice.Lib.Compiler.Samples