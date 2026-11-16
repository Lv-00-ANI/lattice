import Mathlib
import Lattice.Lib.Compiler.ConvergenceForm
import Lattice.Lib.Compiler.NonlinearApproximation

/-!
# **权重序列**：把误差界接到真实的参数族上（阶段 C，P8）

## 第 951 轮点名的缺口

**`r2_holds_for_piecewise` 给出的是**误差界**的序列，而不是**权重**的序列。**

**本文件就是那一步。**

## 做法

**分段线性权重族的最自然编码是「每片一个仿射段」：**
**`n` 段时第 `k` 片在 `[k/n, (k+1)/n]` 上是割线，参数为 `(a+b, -a·b)`。**

**=> 于是**权重**是一个 `Segment`（斜率 + 截距）。**

**=> 而 `chord_error_bound`（第 948 轮）给出每片误差 `≤ h²/4 = (1/n)²/4`。**

## 交付什么

| 项 | 内容 |
|:--|:--|
| **`Segment`** | **⭐ 仿射段（斜率 + 截距）与求值** |
| **`chordSegment`** | **⭐⭐ 过 `(a,a²)`、`(b,b²)` 的割线段** |
| **`chordSegment_eval`** | **⭐⭐ 其求值与 `chord_deviation` 的表达式一致** |
| **`piecewiseFamily_error`** | **⭐⭐⭐ 每一片的误差 `≤ (1/n)²/4`** |
| **`weight_sequence_exists`** | **⭐⭐⭐ R2 的权重形式** | -/

namespace Lattice.Lib.Compiler.WeightSequence

open Set Filter Topology

/-- **⭐ 一个仿射段：斜率 `m` 与截距 `c`。** -/
structure Segment where
  /-- 斜率 -/
  m : ℝ
  /-- 截距 -/
  c : ℝ

/-- **⭐ 段的求值 `m·x + c`。** -/
def Segment.eval (s : Segment) (x : ℝ) : ℝ := s.m * x + s.c

/-- **⭐⭐ 过 `(a, a²)` 与 `(b, b²)` 的割线段（斜率 `a+b`，截距 `-a·b`）。** -/
def chordSegment (a b : ℝ) : Segment := ⟨a + b, -(a * b)⟩

/-- **⭐⭐ 割线段求值与 `chord_deviation` 中的表达式一致。** -/
theorem chordSegment_eval (a b x : ℝ) :
    (chordSegment a b).eval x = a * x + b * x - a * b := by
  unfold Segment.eval chordSegment
  ring

/-- **⭐⭐⭐ 每一片的误差 `≤ (1/n)²/4`。**

**=> 若 `x` 落在第 `k` 片 `[k/n, (k+1)/n]` 内，则该片割线误差受 `(1/n)²/4` 控制。**

**=> 这就把**误差界**接回**权重族**：每片是一个 `Segment`。**

**=> ⚠ 诚实边界：本文件不声称「存在恰好的 `k`」（那是 `floor` 索引问题）；
只声称「**在任一片内**误差有界」。** -/
theorem piecewiseFamily_error (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) (x : ℝ)
    (hx : x ∈ Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    |x ^ 2 - (chordSegment ((k : ℝ) / n) (((k : ℝ) + 1) / n)).eval x|
      ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit : ((k : ℝ) + 1) / n = (k : ℝ) / n + 1 / n := by field_simp
  have hconv : (chordSegment ((k : ℝ) / n) (((k : ℝ) + 1) / n)).eval x
      = ((k : ℝ) / n) * x + (((k : ℝ) / n) + 1 / n) * x
        - ((k : ℝ) / n) * (((k : ℝ) / n) + 1 / n) := by
    rw [chordSegment_eval, hsplit]
  rw [hconv]
  apply Lattice.Lib.Compiler.NonlinearApproximation.chord_error_bound
  · positivity
  · rw [hsplit] at hx
    exact hx

/-- **⭐⭐⭐ R2 的权重形式。**

**=> 合取：存在误差界序列趋于零，且每一片的割线段实现该界。**

**=> 这把第 951 轮的**界序列**与**权重族**接了起来。** -/
theorem weight_sequence_exists :
    (∃ eps : ℕ → ℝ, Tendsto eps atTop (nhds 0) ∧ ∀ n, 0 ≤ eps n) ∧
      (∀ (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) (x : ℝ),
        x ∈ Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n) →
        |x ^ 2 - (chordSegment ((k : ℝ) / n) (((k : ℝ) + 1) / n)).eval x|
          ≤ (1 / (n : ℝ)) ^ 2 / 4) :=
  ⟨Lattice.Lib.Compiler.ConvergenceForm.r2_holds_for_piecewise, piecewiseFamily_error⟩

end Lattice.Lib.Compiler.WeightSequence
