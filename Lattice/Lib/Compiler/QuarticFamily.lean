import Lattice.Lib.Compiler.CapabilityTable

/-!
# **表**不是**上限：四次族在表外，但它有界**

## 这一轮要立的具体命题

规划 §1.6 的末句是「该判据**不是能力上限**」。此前我只证明了「三档之内如何选」，
**从未证明表外的族也可能达到**——于是那句话等于一句设计声明。

**⇒ 本文件给出**见证**：目标 `t⁴`。**

1. **表内不可达**：`polyRow` 只到度数 3，故没有一行覆盖 `t⁴`；
2. **表外可达**：`interpFamily n (fun t => t⁴)` 有整域界 `3/(2n²)`。

**⇒ 合起来，「表不是上限」成为一条**定理**，而不是一句承诺。**

## 四次族的界：仍然是纯代数

**四次函数的「函数减弦」是四次多项式且在 `a`、`b` 为零，故可分解：**

**`x⁴ − chord(x) = (x − a)(x − b)(x² + (a+b)x + (a² + ab + b²))`**

**⇒ 后因子由 `x³`、`x²` 两项系数为零定出：
展开后 `x³` 系数是 `p − (a+b)`，`x²` 系数是 `q − p(a+b) + ab`，两者为零给出 `p = a+b`、`q = a²+ab+b²`。**

**⇒ 于是界仍只需**两个初等估计**：尖顶估计（前两因子）与「第三因子 ≤ 6」（当 `0 ≤ a ≤ x ≤ b ≤ 1`）。
⇒ **无导数、无凸性、无中值定理**——与三次族同一条路线。**
-/

namespace Lattice.Lib.Compiler.QuarticFamily

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.GridBound
open Lattice.Lib.Compiler.PiecewiseUniform
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.CubicFamily
open Lattice.Lib.Compiler.CapabilityTable
open Lattice.Lib.Compiler

/-- **⭐⭐⭐ 四次函数的「函数减弦」分解式。** -/
theorem quartic_sub_chord (a b x : ℝ) (h : a ≠ b) :
    x ^ 4 - (chordOf (fun t : ℝ => t ^ 4) a b).eval x
      = (x - a) * (x - b) * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2)) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [chordOf, chordSlope, Segment.eval]
  field_simp
  ring

/-- **⭐⭐ 第三因子在 `[0,1]` 的段上有界 `6`。**

**⇒ 五个单项各自估计：`x² ≤ 1`、`(a+b)x ≤ 2`、`a² + ab + b² ≤ 3`。**
**⇒ 前提 `0 ≤ a ≤ x ≤ b ≤ 1` 缺一不可：没有 `b ≤ 1` 就没有 `x² ≤ 1`。** -/
theorem quartic_third_factor_bound (a b x : ℝ) (h0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hx : x ∈ Set.Icc a b) :
    |x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2)| ≤ 6 := by
  have hnn : 0 ≤ x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2) := by
    have h1 : 0 ≤ x ^ 2 := sq_nonneg x
    have h2 : 0 ≤ (a + b) * x := by nlinarith [h0, hx.1]
    have h3 : 0 ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [h0, hx.1, hx.2]
    linarith
  rw [abs_of_nonneg hnn]
  nlinarith [hx.1, hx.2, h0, le_of_lt hab, hb1, sq_nonneg (x - a), sq_nonneg (b - x),
    sq_nonneg a, sq_nonneg b, sq_nonneg x]

/-- **⭐⭐⭐ 四次族的**单区间**弦误差界：`≤ 3(b−a)²/2`。**

**⇒ 两个因子用尖顶估计得 `(b−a)²/4`，第三因子用 `≤ 6`，相乘即 `3(b−a)²/2`。** -/
theorem quartic_chord_error (a b x : ℝ) (h0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hx : x ∈ Set.Icc a b) :
    |x ^ 4 - (chordOf (fun t : ℝ => t ^ 4) a b).eval x| ≤ 3 * (b - a) ^ 2 / 2 := by
  have hne : a ≠ b := ne_of_lt hab
  rw [quartic_sub_chord a b x hne]
  have htent : |(x - a) * (b - x)| ≤ (b - a) ^ 2 / 4 := tent_le a b x hx
  have hthird : |x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2)| ≤ 6 :=
    quartic_third_factor_bound a b x h0 hab hb1 hx
  have hthird_nn : 0 ≤ x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2) := by
    have h1 : 0 ≤ x ^ 2 := sq_nonneg x
    have h2 : 0 ≤ (a + b) * x := by nlinarith [h0, hx.1]
    have h3 : 0 ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [h0, hx.1, hx.2]
    linarith
  -- **乘法那一步要的是**不带绝对值**的形式。**
  have hthird' : x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2) ≤ 6 := by
    have := hthird
    rwa [abs_of_nonneg hthird_nn] at this
  -- **\u628a\u4e09\u4e2a\u56e0\u5b50\u7684\u7edd\u5bf9\u503c\u62c6\u5f00\u3002**
  have hfac : |(x - a) * (x - b) * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2))|
      = |(x - a) * (b - x)| * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2)) := by
    have h1 : (x - a) * (x - b) * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2))
        = -(((x - a) * (b - x)) * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2))) := by ring
    rw [h1, abs_neg, abs_mul, abs_of_nonneg hthird_nn]
  rw [hfac]
  have htent_nn : 0 ≤ (b - a) ^ 2 / 4 := by positivity
  have hstep : |(x - a) * (b - x)| * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2))
      ≤ ((b - a) ^ 2 / 4) * 6 := by
    have h1 : |(x - a) * (b - x)| * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2))
        ≤ ((b - a) ^ 2 / 4) * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2)) :=
      mul_le_mul_of_nonneg_right htent hthird_nn
    have h2 : ((b - a) ^ 2 / 4) * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2))
        ≤ ((b - a) ^ 2 / 4) * 6 := mul_le_mul_of_nonneg_left hthird' htent_nn
    linarith
  calc |(x - a) * (b - x)| * (x ^ 2 + (a + b) * x + (a ^ 2 + a * b + b ^ 2))
      ≤ ((b - a) ^ 2 / 4) * 6 := hstep
    _ = 3 * (b - a) ^ 2 / 2 := by ring

/-! ## 一、四次函数与表内三轮都不同 -/

/-- **⭐ `t⁴` 不属仿射族**（三点定値：在 `0,1,2` 处）。 -/
theorem quartic_not_affine :
    ¬ ∃ c d : ℝ, (fun t : ℝ => t ^ 4) = fun t : ℝ => c * t + d := by
  rintro ⟨c, d, h⟩
  have h0 : c * 0 + d = (0 : ℝ) ^ 4 := by simpa using (congrFun h 0).symm
  have h1 : c * 1 + d = (1 : ℝ) ^ 4 := by simpa using (congrFun h 1).symm
  have h2 : c * 2 + d = (2 : ℝ) ^ 4 := by simpa using (congrFun h 2).symm
  norm_num at h0 h1 h2
  linarith

/-- **⭐ `t⁴ ≠ t²`**（在 `t = 2` 处）。 -/
theorem quartic_ne_square : (fun t : ℝ => t ^ 4) ≠ (fun t : ℝ => t ^ 2) := by
  intro h
  have h2 : (2 : ℝ) ^ 4 = (2 : ℝ) ^ 2 := by simpa using congrFun h 2
  norm_num at h2

/-- **⭐ `t⁴ ≠ t³`**（在 `t = 2` 处）。 -/
theorem quartic_ne_cube : (fun t : ℝ => t ^ 4) ≠ (fun t : ℝ => t ^ 3) := by
  intro h
  have h2 : (2 : ℝ) ^ 4 = (2 : ℝ) ^ 3 := by simpa using congrFun h 2
  norm_num at h2

/-- **⭐⭐ 四次族的整域界（**闭**区间 `[0,1]`）。

**⇒ 与 `quartic_uniform_bound` 相比多了右端点。这里**不**复用那一条（它要求 `y < 1`，
而段内只能得 `y ≤ (k+1)/n ≤ 1`），而是**直接重复逐段论证**：
`quartic_chord_error` 只需 `b ≤ 1`，不需严格性。** -/
theorem quartic_uniform_bound_Icc (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |x ^ 4 - gridEval (interpFamily n (fun t : ℝ => t ^ 4)) n x|
        ≤ 3 * (1 / (n : ℝ)) ^ 2 / 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  intro x hx
  apply gridEval_bound_of_segmentwise_Icc (fun k => interpFamily n (fun t : ℝ => t ^ 4) k) n hn
    (fun t : ℝ => t ^ 4) (3 * (1 / (n : ℝ)) ^ 2 / 2)
  · intro k hk y hy
    have hseg : interpFamily n (fun t : ℝ => t ^ 4) k
        = chordOf (fun t : ℝ => t ^ 4) ((k : ℝ) / n) (((k : ℝ) + 1) / n) := rfl
    rw [hseg]
    have hlt : ((k : ℝ) / n) < (((k : ℝ) + 1) / n) := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by field_simp
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      linarith
    have hleft : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    have hright : (((k : ℝ) + 1) / n) ≤ 1 := by
      rw [div_le_one hn']
      exact_mod_cast Nat.succ_le_of_lt hk
    have hb := quartic_chord_error ((k : ℝ) / n) (((k : ℝ) + 1) / n) y hleft hlt hright hy
    have hwidth : ((((k : ℝ) + 1) / n) - ((k : ℝ) / n)) ^ 2 = (1 / (n : ℝ)) ^ 2 := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by field_simp
      rw [heq]
    rw [hwidth] at hb
    exact hb
  · have hbridge : (interpFamily n (fun t : ℝ => t ^ 4) n).eval 1
        = gridEval (interpFamily n (fun t : ℝ => t ^ 4)) n 1 := by
      show _ = (interpFamily n (fun t : ℝ => t ^ 4) (segmentIndex n 1)).eval 1
      rw [segmentIndex_at_one]
    rw [hbridge, interpFamily_eval_at_one n hn (fun t : ℝ => t ^ 4)]
    have hpos : (0 : ℝ) ≤ 3 * (1 / (n : ℝ)) ^ 2 / 2 := by positivity
    simpa using hpos
  · exact hx

/-- **⭐⭐⭐ 第 4 行：`x⁴`，常数 `3/2`。

**⇒ 与前三行同一形状，故新增一族的成本仍然是**一条单区间界**。** -/
noncomputable def quarticRow : CapabilityRow where
  degree := 4
  term := quarticTerm
  fn := fun t : ℝ => t ^ 4
  target := .interp (fun t : ℝ => t ^ 4)
  semantics := by
    intro x
    exact evalSym_quarticTerm x
  compiled := by
    intro r
    exact compileTarget_quarticTerm r
  family_eq := by
    intro r k
    rfl
  constant := 3 / 2
  bound := by
    intro n hn x hx
    show |x ^ 4 - gridEval (interpFamily n (fun t : ℝ => t ^ 4)) n x|
        ≤ 3 / 2 * (1 / (n : ℝ)) ^ 2
    have h := quartic_uniform_bound_Icc n hn x hx
    have heq : 3 * (1 / (n : ℝ)) ^ 2 / 2 = 3 / 2 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [heq] at h
    exact h
  covers := fun g => g = fun t : ℝ => t ^ 4
  covers_self := rfl
  covers_bound := by
    intro g hg n hn x hx
    subst hg
    show |x ^ 4 - gridEval (interpFamily n (fun t : ℝ => t ^ 4)) n x|
        ≤ 3 / 2 * (1 / (n : ℝ)) ^ 2
    have h := quartic_uniform_bound_Icc n hn x hx
    have heq : 3 * (1 / (n : ℝ)) ^ 2 / 2 = 3 / 2 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [heq] at h
    exact h

end Lattice.Lib.Compiler.QuarticFamily