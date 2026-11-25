import Lattice.Lib.Compiler.PowChord
import Lattice.Lib.Compiler.CapabilityTable

/-!
# **解析能力与符号证据解耦：任意度数都能入表**

## 为什么必须解耦

**`CapabilityRow` 的字段里有 `term : ExprExt` 与 `compiled : compileTarget r term = some target`——
即「这个族有一个**符号代表项**」。**
**⇒ 但 `ExprExt` 只能写**有限嵌套**的 `mul`：`x²`、`x³`、`x⁴` 各需一支规则，**`x^d` 对任意 `d` 写不出来**。**

**⇒ 于是第 1076 轮的一般界 `d(d−1)/8` **无法进入表**，尽管它覆盖所有度数。
⇒ 这不是定理不够，而是**表的结构要求过强**。**

## 修法：分两层

| 层 | 结构 | 需要什么 |
|:--|:--|:--|
| **解析层** | `AnalyticRow` | 函数、族、常数、界——**不要求符号项** |
| **能力层** | `CapabilityRow` | 解析层 **+** 符号代表项与编译证据 |

**⇒ 于是 `powAnalyticRow d hd` 对**任意** `d ≥ 2` 存在，而 `analytic_of_capability` 说明
已有的四行**都**在解析层里有对应物——即符号层是解析层的**加细**，而不是另一套。**

**⇒ 这也解释了为什么「选择」本不需要符号证据：选择比较的是 `covers` 与 `constant`，
两者都在解析层；符号证据只在**追溯到源语言**时才需要。**
-/

namespace Lattice.Lib.Compiler.AnalyticRow

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.GridBound
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.PiecewiseUniform
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.CapabilityTable
open Lattice.Lib.Compiler.PowChord

/-- **解析能力行**：一个函数、它覆盖的族、一个常数与一条整域界。

**⇒ 与 `CapabilityRow` 的区别是**没有** `term` / `compiled` / `family_eq`：
⇒ 因此它可以描述**任意**族，包括 `ExprExt` 写不出来的那些。** -/
structure AnalyticRow where
  /-- The degree of the monomial this row covers. -/
  degree : ℕ
  /-- The representative function. -/
  fn : ℝ → ℝ
  /-- The constant `C` in `error <= C / n^2`. -/
  constant : ℝ
  /-- **The family this row covers.** -/
  covers : (ℝ → ℝ) → Prop
  /-- The representative belongs to the family it covers. -/
  covers_self : covers fn
  /-- **The bound holds for EVERY member of the family.** -/
  covers_bound : ∀ g : ℝ → ℝ, covers g → ∀ (n : ℕ), 0 < n → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |g x - gridEval (interpFamily n g) n x| ≤ constant * (1 / (n : ℝ)) ^ 2

/-- **⭐⭐ 一般幂次的**闭区间**界**（把它搬进 `Icc` 以便与解析行的域一致）。

**⇒ 与 `pow_uniform_bound` 相比多了右端点；右端点由 `interpFamily_eval_at_one` 归零。** -/
theorem pow_uniform_bound_Icc (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |x ^ d - gridEval (interpFamily n (fun t : ℝ => t ^ d)) n x|
        ≤ ((d * (d - 1) : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2 / 8 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  intro x hx
  apply gridEval_bound_of_segmentwise_Icc (fun k => interpFamily n (fun t : ℝ => t ^ d) k) n hn
    (fun t : ℝ => t ^ d) (((d * (d - 1) : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2 / 8)
  · intro k hk y hy
    have hseg : interpFamily n (fun t : ℝ => t ^ d) k
        = chordOf (fun t : ℝ => t ^ d) ((k : ℝ) / n) (((k : ℝ) + 1) / n) := rfl
    rw [hseg]
    have hlt : ((k : ℝ) / n) < (((k : ℝ) + 1) / n) := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by field_simp
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      linarith
    have hleft : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    have hright : (((k : ℝ) + 1) / n) ≤ 1 := by
      rw [div_le_one hn']
      exact_mod_cast Nat.succ_le_of_lt hk
    have hb := pow_chord_error d hd ((k : ℝ) / n) (((k : ℝ) + 1) / n) y hleft hlt hright hy
    have hwidth : ((((k : ℝ) + 1) / n) - ((k : ℝ) / n)) ^ 2 = (1 / (n : ℝ)) ^ 2 := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by field_simp
      rw [heq]
    rw [hwidth] at hb
    exact hb
  · have hbridge : (interpFamily n (fun t : ℝ => t ^ d) n).eval 1
        = gridEval (interpFamily n (fun t : ℝ => t ^ d)) n 1 := by
      show _ = (interpFamily n (fun t : ℝ => t ^ d) (segmentIndex n 1)).eval 1
      rw [segmentIndex_at_one]
    rw [hbridge, interpFamily_eval_at_one n hn (fun t : ℝ => t ^ d)]
    have hpos : (0 : ℝ) ≤ ((d * (d - 1) : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2 / 8 := by positivity
    simpa using hpos
  · exact hx

/-- **⭐⭐⭐ 任意幂次的解析行**：`powAnalyticRow d hd` 对**任意** `d ≥ 2` 存在。

**⇒ 这是解耦的收益：表**不再被 `ExprExt` 的表达力卡住**。
⇒ 常数就是**闭式** `d(d−1)/8`，不是逐档凑出来的。** -/
noncomputable def powAnalyticRow (d : ℕ) (hd : 2 ≤ d) : AnalyticRow where
  degree := d
  fn := fun t : ℝ => t ^ d
  constant := ((d * (d - 1) : ℕ) : ℝ) / 8
  covers := fun g => g = fun t : ℝ => t ^ d
  covers_self := rfl
  covers_bound := by
    intro g hg n hn x hx
    subst hg
    show |(fun t : ℝ => t ^ d) x - gridEval (interpFamily n (fun t : ℝ => t ^ d)) n x|
        ≤ ((d * (d - 1) : ℕ) : ℝ) / 8 * (1 / (n : ℝ)) ^ 2
    have h := pow_uniform_bound_Icc d hd n hn x hx
    have heq : ((d * (d - 1) : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2 / 8
        = ((d * (d - 1) : ℕ) : ℝ) / 8 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [heq] at h
    exact h

/-- **⭐⭐ 符号层是解析层的**加细**：每个能力行都给出一个解析行。** -/
noncomputable def analytic_of_capability (row : CapabilityRow) : AnalyticRow where
  degree := row.degree
  fn := row.fn
  constant := row.constant
  covers := row.covers
  covers_self := row.covers_self
  covers_bound := row.covers_bound

/-! ## \u4e00\u3001\u5b83\u7684\u610f\u4e49\uff1a\u65b0\u5ea6\u6570\u5f97\u5230\u4e86**\u514d\u8d39\u7684\u754c** -/

/-- **\u2b50\u2b50\u2b50 \u4e94\u6b21\u5e42\u7684\u754c\uff1a`\u2264 5/2\u00b7(1/n)\u00b2`**\u2014\u2014**\u6ca1\u6709\u4efb\u4f55\u65b0\u7684\u5206\u89e3\u6216\u6c42\u5bfc\u3002

**\u21d2 \u4e94\u6b21\u65cf\u5728\u672c\u9879\u76ee\u91cc**\u4ece\u672a\u88ab\u5355\u72ec\u5904\u7406**\uff1a\u5b83\u76f4\u63a5\u4ece `powAnalyticRow 5` \u843d\u4e0b\u6765\u3002
\u21d2 \u800c `5\u00b74/8 = 5/2`\u3002** -/
theorem quintic_bound (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |x ^ 5 - gridEval (interpFamily n (fun t : ℝ => t ^ 5)) n x|
        ≤ ((5 * (5 - 1) : ℕ) : ℝ) / 8 * (1 / (n : ℝ)) ^ 2 :=
  (powAnalyticRow 5 (by norm_num)).covers_bound (fun t : ℝ => t ^ 5) rfl n hn

/-- **⭐ 五次幂的常数就是 `5/2`。** -/
theorem quintic_constant : (((5 * (5 - 1) : ℕ)) : ℝ) / 8 = 5 / 2 := by norm_num

/-- **⭐⭐⭐ 十次幂的界**——同样**零新工作**。

**⇒ 这一条用于说明「任意度数」不是修辞：`d = 10` 确实得到一个具体常数。** -/
theorem tenth_power_bound (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |x ^ 10 - gridEval (interpFamily n (fun t : ℝ => t ^ 10)) n x|
        ≤ ((10 * (10 - 1) : ℕ) : ℝ) / 8 * (1 / (n : ℝ)) ^ 2 :=
  (powAnalyticRow 10 (by norm_num)).covers_bound (fun t : ℝ => t ^ 10) rfl n hn

/-- **⭐ 十次幂的常数就是 `45/4`。** -/
theorem tenth_power_constant : (((10 * (10 - 1) : ℕ)) : ℝ) / 8 = 45 / 4 := by norm_num

end Lattice.Lib.Compiler.AnalyticRow