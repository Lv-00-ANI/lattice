import Lattice.Lib.Compiler.GridBound

/-!
# **第二个真族：三次项 `t ↦ t³`，一条纯代数的弦误差界**

## 为什么这条界**不需要**分析

**三次函数的「函数减弦」是一个三次多项式，且在 `a`、`b` 两处为零 ⇒ 它可以**分解**：**

**`x³ − chord(x) = (x − a)(x − b)(x + a + b)`**

**⇒ 最后一个因子由「`x²` 项系数为零」定出：右侧展开的 `x²` 系数是 `−(a + b + r)`，
而左侧 `x³ − 线性函数` 的 `x²` 系数是 `0`，故 `r = −(a + b)`。**

**⇒ 有了这条分解式，误差界就只剩**两个初等的乘积估计**（与导数、凸性、中值定理全无关系）：

1. `|(x − a)(x − b)| ≤ (b − a)²/4`（**尖顶估计**，`u·v ≤ ((u+v)/2)²`）；
2. `|x + a + b| ≤ 3b`（当 `0 ≤ a ≤ x ≤ b`）。

**⇒ 于是三次族的上界是 `3b(b−a)²/4`，而整域界（`b ≤ 1`）为 `3/(4n²)`。**

## 这一步在整条链里是什么位置

**第 1058 轮的桥与第 1057 轮的加权界合起来，把「新增一族」的成本压到**一条单区间界**。
本文件就是那一条——**这是「入口真的能用」的第一次兑现**，而第 1059 轮只是对旧族做了二次验证。
-/

namespace Lattice.Lib.Compiler.CubicFamily

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler

/-- **⭐⭐⭐ 三次函数的「函数减弦」分解式。**

**⇒ `x³ − chord(x) = (x − a)(x − b)(x + a + b)`，对**任意** `a ≠ b` 成立。**
**⇒ 这是本文件唯一需要算的东西；其余全是乘积估计。** -/
theorem cube_sub_chord (a b x : ℝ) (h : a ≠ b) :
    x ^ 3 - (chordOf (fun t : ℝ => t ^ 3) a b).eval x
      = (x - a) * (x - b) * (x + a + b) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [chordOf, chordSlope, Segment.eval]
  field_simp
  ring

/-- **⭐ 尖顶估计**：`|(x − a)(b − x)| ≤ (b − a)²/4`。

**⇒ 证明只用 `u·v ≤ ((u+v)/2)²`，即 `(u−v)² ≥ 0`。**
**⇒ 这是 `x²` 弦误差那条界（`sq_chord_error_eq_tent`）背后的同一个不等式，这里单独命名。** -/
theorem tent_le (a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    |(x - a) * (b - x)| ≤ (b - a) ^ 2 / 4 := by
  have hnn1 : 0 ≤ x - a := by linarith [hx.1]
  have hnn2 : 0 ≤ b - x := by linarith [hx.2]
  have hprod : (x - a) * (b - x)
      = (((x - a) + (b - x)) ^ 2 - ((x - a) - (b - x)) ^ 2) / 4 := by ring
  have hsum : (x - a) + (b - x) = b - a := by ring
  have hsq : 0 ≤ ((x - a) - (b - x)) ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (mul_nonneg hnn1 hnn2), hprod, hsum]
  nlinarith

/-- **⭐⭐⭐ 三次族的**单区间**弦误差界。**

**⇒ `|x³ − chord| ≤ 3b(b−a)²/4`，前提 `0 ≤ a < b`、`x ∈ [a,b]`。**
**⇒ 三个因子分别估计：前两个用尖顶估计 `(b−a)²/4`，第三个用 `x + a + b ≤ 3b`。** -/
theorem cube_chord_error (a b x : ℝ) (h0 : 0 ≤ a) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    |x ^ 3 - (chordOf (fun t : ℝ => t ^ 3) a b).eval x| ≤ 3 * b * (b - a) ^ 2 / 4 := by
  have hne : a ≠ b := ne_of_lt hab
  rw [cube_sub_chord a b x hne]
  -- **第一于二个因子：尖顶估计。**
  have htent : |(x - a) * (b - x)| ≤ (b - a) ^ 2 / 4 := tent_le a b x hx
  -- **第三个因子：非负且 ≤ 3b。**
  have hthird_nn : 0 ≤ x + a + b := by linarith [h0, hx.1, hx.2, le_of_lt hab]
  have hthird : x + a + b ≤ 3 * b := by linarith [h0, hx.1, hx.2]
  have hthird_abs : |x + a + b| = x + a + b := abs_of_nonneg hthird_nn
  -- **把三个因子的绝对值拆开；负号在乘积**内部**，故先把它提到整体。**
  have hfac : |(x - a) * (x - b) * (x + a + b)| = |(x - a) * (b - x)| * (x + a + b) := by
    have h1 : (x - a) * (x - b) * (x + a + b)
        = -(((x - a) * (b - x)) * (x + a + b)) := by ring
    rw [h1, abs_neg, abs_mul, hthird_abs]
  rw [hfac]
  have hstep : |(x - a) * (b - x)| * (x + a + b) ≤ 3 * b * (b - a) ^ 2 / 4 := by
    have h1 : |(x - a) * (b - x)| * (x + a + b) ≤ ((b - a) ^ 2 / 4) * (x + a + b) :=
      mul_le_mul_of_nonneg_right htent hthird_nn
    have h2 : ((b - a) ^ 2 / 4) * (x + a + b) ≤ ((b - a) ^ 2 / 4) * (3 * b) := by
      apply mul_le_mul_of_nonneg_left hthird
      positivity
    have h3 : ((b - a) ^ 2 / 4) * (3 * b) = 3 * b * (b - a) ^ 2 / 4 := by ring
    linarith
  exact hstep

/-- **⭐⭐⭐ 三次族的**整域一致界**：`≤ 3·(1/n)²/4`。**

**⇒ 路径就是「一族一装」的入口：`cube_chord_error`（单区间）
+ `gridEval_bound_of_segmentwise`（分段→整域）。**
**⇒ 段宽为 `1/n`，且 `b = (k+1)/n ≤ 1`，故界退化为 `3·(1/n)²/4`——与 `n` 无关的那部分正是效率所在。** -/
theorem cube_uniform_bound (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |x ^ 3 - gridEval (interpFamily n (fun t : ℝ => t ^ 3)) n x|
        ≤ 3 * (1 / (n : ℝ)) ^ 2 / 4 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  intro x hx
  apply Lattice.Lib.Compiler.GridBound.gridEval_bound_of_segmentwise
    (fun k => interpFamily n (fun t : ℝ => t ^ 3) k) n hn
    (fun t : ℝ => t ^ 3) (3 * (1 / (n : ℝ)) ^ 2 / 4)
  · intro k hk y hy
    -- **该段就是该区间上的弦。**
    have hseg : interpFamily n (fun t : ℝ => t ^ 3) k
        = chordOf (fun t : ℝ => t ^ 3) ((k : ℝ) / n) (((k : ℝ) + 1) / n) := rfl
    rw [hseg]
    -- **区间非空，且左端非负。**
    have hlt : ((k : ℝ) / n) < (((k : ℝ) + 1) / n) := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by
        field_simp
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      linarith
    have hleft : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    have hb := cube_chord_error ((k : ℝ) / n) (((k : ℝ) + 1) / n) y hleft hlt hy
    -- **幅度与右端归一化。**
    have hwidth : ((((k : ℝ) + 1) / n) - ((k : ℝ) / n)) ^ 2 = (1 / (n : ℝ)) ^ 2 := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by
        field_simp
      rw [heq]
    have hright : (((k : ℝ) + 1) / n) ≤ 1 := by
      rw [div_le_one hn']
      exact_mod_cast Nat.succ_le_of_lt hk
    have hbound : 3 * (((k : ℝ) + 1) / n) * ((((k : ℝ) + 1) / n) - ((k : ℝ) / n)) ^ 2 / 4
        ≤ 3 * (1 / (n : ℝ)) ^ 2 / 4 := by
      rw [hwidth]
      have hpos : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ 2 / 4 := by positivity
      nlinarith [hright]
    linarith
  · -- **域假设是 `apply` 留下的第二个目标。**
    exact hx

end Lattice.Lib.Compiler.CubicFamily