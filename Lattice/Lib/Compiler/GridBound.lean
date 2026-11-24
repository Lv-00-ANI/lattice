import Lattice.Lib.Compiler.LinearComb
import Lattice.Lib.Compiler.PiecewiseWeights
import Lattice.Lib.Compiler.ChordErrorGeneral

/-!
# **分段界 → 整域界：让「一族」只要给出**每段**的界，就自动得到整域界**

## 补的是哪一段接线

第 1057 轮的 `linComb_error` 与既有的弦误差定理都是**单区间**陈述（在 `[a,b]` 上一次弦）。
而产物的 `evalAt` 走的是 `gridEval`：按 `segmentIndex n x` **选一段**求值。
**⇒ 二者之间缺一条桥：分段界如何变成整域界。**

**⇒ 本文件的 `gridEval_bound_of_segmentwise` 就是这条桥：**
若每一段 `[k/n, (k+1)/n]` 上 `f` 与该段线性函数的差不超过 `B`，
则整个 `[0,1]` 上 `f` 与 `gridEval g n` 的差也不超过 `B`。

**⇒ 有了它，「一族」的交付物就统一为：给出 **`B`** 与**每段的弦误差**，整域界自动得到。**

## 这条桥的证明只有两个事实

1. `segmentIndex_lt`：`x < 1` 时选中的段号 `< n`（故「每段」的假设可用）；
2. `segmentIndex_bounds`：`x` **确实落在**选中的那一段内（本文件新证，由既有的
   `segmentIndex_mem` 除 `n > 0` 得到）。
-/

namespace Lattice.Lib.Compiler.GridBound

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler

/-- **⭐⭐ `x` 落在被选中的那一段内。**

**⇒ 由既有 `segmentIndex_mem`（交叉相乘形式 `k ≤ x·n < k+1`）两边同除 `n > 0` 得到。
⇒ 把「交叉相乘」换成「区间」，是因为区间形式才能直接喂给 `chordOf` 的引理。** -/
theorem segmentIndex_bounds (n : ℕ) (hn : 0 < n) (x : ℝ) (hx0 : 0 ≤ x) :
    x ∈ Set.Icc (((segmentIndex n x : ℕ) : ℝ) / n)
        (((((segmentIndex n x : ℕ) : ℝ) + 1)) / n) := by
  obtain ⟨hlo, hhi⟩ := segmentIndex_mem n x hx0
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  constructor
  · rw [div_le_iff₀ hn']
    linarith
  · rw [le_div_iff₀ hn']
    linarith

/-- **⭐⭐⭐ 分段界 ⟹ 整域界。**

**⇒ 域取 `Ico 0 1` 而不是 `Icc 0 1`，因为 `x = 1` 时 `segmentIndex n 1 = n`
（`segmentIndex_at_one`）——**第 `n` 段不存在**。
把这个界写成半开区间，而不是在证明里偷偷假设 `x < 1`。** -/
theorem gridEval_bound_of_segmentwise (g : ℕ → Segment) (n : ℕ) (hn : 0 < n)
    (f : ℝ → ℝ) (B : ℝ)
    (hseg : ∀ k, k < n → ∀ y ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        |f y - (g k).eval y| ≤ B)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    |f x - gridEval g n x| ≤ B := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x < 1 := hx.2
  have hlt : segmentIndex n x < n := segmentIndex_lt n hn x hx0 hx1
  have hmem := segmentIndex_bounds n hn x hx0
  have := hseg (segmentIndex n x) hlt x hmem
  simpa [gridEval] using this

/-- **⭐⭐⭐ 复用验证：`x²` 的**整域**界由 `gridEval_bound_of_segmentwise` 重推出来。**

**⇒ 逐段的界来自既有的 `chord_error_sq_rederived`（单区间），
再归一化 `(k+1)/n − k/n = 1/n`。**

**⇒ 结论与既有 `interpFamily_sq_error` **逐字相同**；差别在于路径：
本条经**桥**（分段→整域），而旧条直接用 `irWeights_error_bound`。
**⇒ 两条都对，而后者可以**为任何族**所用——这就是「一族一装」的入口。** -/
theorem sq_gridEval_error_via_segmentwise (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    |(fun t : ℝ => t * t) x - gridEval (interpFamily n (fun t : ℝ => t * t)) n x|
      ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  apply gridEval_bound_of_segmentwise (fun k => interpFamily n (fun t : ℝ => t * t) k)
    n hn (fun t : ℝ => t * t) ((1 / (n : ℝ)) ^ 2 / 4)
  intro k _hk y hy
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- **该段就是那个区间上的弦。**
  have hch : interpFamily n (fun t : ℝ => t * t) k
      = chordOf (fun t : ℝ => t ^ 2) ((k : ℝ) / n) (((k : ℝ) + 1) / n) := by
    show chordOf (fun t : ℝ => t * t) ((k : ℝ) / n) (((k : ℝ) + 1) / n) = _
    congr 1
    funext t
    rw [pow_two]
  rw [hch]
  have hy2 : y * y = y ^ 2 := by rw [pow_two]
  rw [hy2]
  -- **区间非空：`k/n < (k+1)/n`。**
  have hlt : ((k : ℝ) / n) < (((k : ℝ) + 1) / n) := by
    have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by
      field_simp
    linarith
  have hb := Lattice.Lib.Compiler.ChordErrorGeneral.chord_error_sq_rederived
    ((k : ℝ) / n) (((k : ℝ) + 1) / n) y hlt hy
  -- **幅度归一化：`((k+1)/n − k/n)²/4 = (1/n)²/4`。**
  have hnorm : ((((k : ℝ) + 1) / n) - ((k : ℝ) / n)) ^ 2 / 4 = (1 / (n : ℝ)) ^ 2 / 4 := by
    have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by
      field_simp
    rw [heq]
  rw [hnorm] at hb
  exact hb
  -- **域假设是 `apply` 留下的第二个目标。**
  exact hx

end Lattice.Lib.Compiler.GridBound