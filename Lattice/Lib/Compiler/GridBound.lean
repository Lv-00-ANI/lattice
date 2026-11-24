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
open Lattice.Lib.Compiler.LinearComb
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

/-! ## 三、一般二次项走新入口 -/

/-- **⭐⭐一般二次项在**任意区间**上的弦误差界。**

**⇒ 拆成**两支**（`t·t` 系数 `a`，仿射系数 1），然后**一步 `linComb_error`**。**

**⇒ 索引用 `Finset ℕ` 的 `{0, 1}`，而不是 `Fin 2`：
前者的 `simp` 归一化形状稳定，后者需要 `Fin.reduceEq` 的形状知识。** -/
theorem quadFun_chord_error_on_interval (a p q u v : ℝ) (huv : u < v) (y : ℝ)
    (hy : y ∈ Set.Icc u v) :
    |quadFun a p q y - (chordOf (quadFun a p q) u v).eval y|
      ≤ |a| * ((v - u) ^ 2 / 4) := by
  have hne : u ≠ v := ne_of_lt huv
  let s : Finset ℕ := {0, 1}
  let c : ℕ → ℝ := fun i => if i = 0 then a else 1
  let b : ℕ → ℝ → ℝ := fun i y' => if i = 0 then y' * y' else p * y' + q
  let B : ℕ → ℝ := fun i => if i = 0 then (v - u) ^ 2 / 4 else 0
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  have h10 : ¬ ((1 : ℕ) = 0) := by norm_num
  -- **两支之和就是 `quadFun`。**
  have hcomb : linComb s c b = quadFun a p q := by
    funext y'
    simp only [linComb, s, c, b, quadFun, Finset.sum_pair h01]
    simp only [if_true, h10, if_false]
    ring
  -- **各支的界。**
  have hB : ∀ i ∈ s, ∀ z ∈ Set.Icc u v,
      |b i z - (chordOf (b i) u v).eval z| ≤ B i := by
    intro i hi z hz
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · -- **第一支：`y·y`，用单区间界。**
      show |(fun t : ℝ => t * t) z
            - (chordOf (fun t : ℝ => t * t) u v).eval z| ≤ (v - u) ^ 2 / 4
      have hch : chordOf (fun t : ℝ => t * t) u v = chordOf (fun t : ℝ => t ^ 2) u v := by
        congr 1
        funext t
        rw [pow_two]
      rw [hch]
      -- **lambda 要先 beta 归约；`rw` 不会自己做这件事。**
      change |z * z - (chordOf (fun t : ℝ => t ^ 2) u v).eval z| ≤ (v - u) ^ 2 / 4
      rw [← pow_two z]
      exact Lattice.Lib.Compiler.ChordErrorGeneral.chord_error_sq_rederived u v z huv hz
    · -- **第二支：仿射，弦精确。**
      show |(fun t : ℝ => p * t + q) z
            - (chordOf (fun t : ℝ => p * t + q) u v).eval z| ≤ 0
      rw [chordOf_affine p q u v hne]
      simp [Segment.eval]
  have hmain := linComb_error s c b B u v hne hB
  rw [hcomb] at hmain
  -- **加权和归一化：`|a|·((v−u)²/4) + 1·0`。**
  have hsum : (∑ i ∈ s, |c i| * B i) = |a| * ((v - u) ^ 2 / 4) := by
    simp only [s, c, B, Finset.sum_pair h01]
    simp only [if_true, h10, if_false]
    norm_num
  rw [hsum] at hmain
  exact hmain y hy

/-- **⭐⭐⭐ 一般二次项的**整域上一致**界——经新入口（桥 + `linComb_error`）。**

**⇒ 语序「对**所有** `x ∈ [0,1)` 成立」，而不是「给定 `x` 时成立」。
**这是一个**严格不同的陈述形状**（结论以 `∀` 开头），而且更好用：
调用者不必自己挑点。**
**⇒ 与旧的 `interpFamily_quadFun_error`（`Icc` 域，方挑点）不是同一个陈述：
本条的域是**半开**的，因为桥需要 `x < 1`。** -/
theorem quadFun_gridEval_uniform_bound (a p q : ℝ) (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |quadFun a p q x - gridEval (interpFamily n (quadFun a p q)) n x|
        ≤ |a| * ((1 / (n : ℝ)) ^ 2 / 4) := by
  intro x hx
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply gridEval_bound_of_segmentwise (fun k => interpFamily n (quadFun a p q) k) n hn
    (quadFun a p q) (|a| * ((1 / (n : ℝ)) ^ 2 / 4))
  · intro k _hk y hy
    -- **该段就是该区间上的弦。**
    have hseg : interpFamily n (quadFun a p q) k
        = chordOf (quadFun a p q) ((k : ℝ) / n) (((k : ℝ) + 1) / n) := rfl
    rw [hseg]
    -- **区间非空。**
    have hlt : ((k : ℝ) / n) < (((k : ℝ) + 1) / n) := by
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by
        field_simp
      linarith
    have hb := quadFun_chord_error_on_interval a p q ((k : ℝ) / n) (((k : ℝ) + 1) / n)
      hlt y hy
    -- **幅度归一化。**
    have hnorm : ((((k : ℝ) + 1) / n) - ((k : ℝ) / n)) ^ 2 / 4
        = (1 / (n : ℝ)) ^ 2 / 4 := by
      have heq : (((k : ℝ) + 1) / n) - ((k : ℝ) / n) = 1 / (n : ℝ) := by
        field_simp
      rw [heq]
    rw [hnorm] at hb
    exact hb
  · exact hx

end Lattice.Lib.Compiler.GridBound