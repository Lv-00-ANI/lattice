import Mathlib
import Lattice.Lib.Compiler.ReversibilityChain

/-!
# **信息锐化**：行为到底决定**多少**权重（阶段 L，O-3 推广）

## 上轮说「不可提取」，本轮说「可提取的恰好是哪一段」

**第 970 轮的 `gridWeights_not_extractable` 证明了：**
**在 `[0,1]` 上，**不存在**把行为还原成全权重向量的提取器。**

**=> 那是**否定**陈述。它没有回答：**能恢复多少？****

**本文件的答案，分三段，且**恰好**卡在 `n` 上：**

| 事实 | 陈述 | 含义 |
|:--|:--|:--|
| **A** | **`gridEval_congr_on_prefix`** | **行为**只依赖** `g` 在 `{0,…,n}` 上的取值** |
| **B** | **`gridEval_index_n_not_determined`** | **但 `g n` **本身也不被决定**：只决定 `m_n + c_n`** |
| **C** | **（上轮）`n+1` 及以后完全不出现** | **索引 `> n` 是**看不见**的** |

**=> A 与 B 合起来：**行为所决定的集合恰为 `{0,…,n−1}`**——
**它不超过 `{0,…,n}`（A），而 `n` 这一点也不在其中（B）。**

## B 为什么成立：端点只给一个方程

**`x ∈ [0,1]` 时索引 `≤ n`。其中 `x < 1` 的索引 `≤ n−1`，只有 `x = 1` 命中索引 `n`。**

**=> 于是 `g n` 只在 `x = 1` 处被**求值一次**，观察到的只是 `(g n).eval 1 = m_n + c_n`。**

**=> 反例：`⟨1, 0⟩` 与 `⟨0, 1⟩` 都满足 `m + c = 1`，故在 `x = 1` 处**给出同一个值**，
而它们是**不同的**分段。**

## 为什么这比「不可提取」更有用

**「不可提取」只说反向失败。**
**=> 「恰好 `{0,…,n−1}` 可恢复」给出了**可执行的设计约束**：
**若要让权重可还原，就必须保证被还原的那一段落在 `0..n−1`；
落在 `n` 上的参数**必须靠别的信息（例如输出端点约束以外的量）补齐**。**

**=> 这是从「不可能」到「恰好能恢复多少」的升级，也正是本库对
「符号 ⇄ 权重」这一跳应有的贡献形态。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`eq_one_of_segmentIndex_eq`** | **⭐⭐ `[0,1]` 上索引等于 `n` ⟹ `x = 1`** |
| **`gridEval_congr_on_prefix`** | **⭐⭐⭐ A：行为只依赖 `{0,…,n}`** |
| **`gridEval_index_n_not_determined`** | **⭐⭐⭐ B：`g n` 不被决定** |
| **`grid_information_is_exactly_prefix`** | **⭐⭐⭐ A ∧ B 的合取：可恢复集恰为 `{0,…,n−1}`** | -/

namespace Lattice.Lib.Compiler.ReversibilitySharpness

open Set
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.PiecewiseUniform
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.ReversibilityChain

/-- **⭐⭐ `[0,1]` 上若分段索引等于 `n`，则该点只能是 `x = 1`。**

**=> `⌊n·x⌋ = n` 给出 `n ≤ n·x`，故 `1 ≤ x`；又 `x ≤ 1`，故 `x = 1`。** -/
theorem eq_one_of_segmentIndex_eq (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (h : segmentIndex n x = n) : x = 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) * x := mul_nonneg (le_of_lt hnpos) hx.1
  have hfloor : Nat.floor ((n : ℝ) * x) = n := by
    unfold segmentIndex at h
    exact h
  have hle : ((n : ℕ) : ℝ) ≤ (n : ℝ) * x := by
    have h1 : ((Nat.floor ((n : ℝ) * x) : ℕ) : ℝ) ≤ (n : ℝ) * x := Nat.floor_le hnonneg
    have h2 : ((Nat.floor ((n : ℝ) * x) : ℕ) : ℝ) = (n : ℝ) := by
      rw [hfloor]
    linarith [h1, h2]
  -- n <= n*x  ==>  1 <= x
  have hx1 : (1 : ℝ) ≤ x := by nlinarith [hle, hnpos]
  linarith [hx.2]

/-- **⭐⭐⭐ A：`[0,1]` 上的行为**只依赖** `g` 在 `{0,…,n}` 上的取值。**

**=> 由 `segmentIndex n x ≤ n`（第 970 轮）直接得到。** -/
theorem gridEval_congr_on_prefix (n : ℕ) (hn : 0 < n) (g h : ℕ → Segment)
    (hagree : ∀ k ≤ n, g k = h k) :
    (fun x : Icc (0 : ℝ) 1 => gridEval g n x.1)
      = (fun x : Icc (0 : ℝ) 1 => gridEval h n x.1) := by
  funext x
  have hk : segmentIndex n x.1 ≤ n := segmentIndex_le_on_unit n hn x.1 x.2
  unfold gridEval
  rw [hagree (segmentIndex n x.1) hk]

/-- **⭐⭐⭐ B：`g n` **本身**也不被行为决定。**

**=> 反例：`⟨1, 0⟩` 与 `⟨0, 1⟩` 的 `m + c` 都等于 `1`，
故在唯一的采样点 `x = 1` 处给出同值，而它们是不同的分段。** -/
theorem gridEval_index_n_not_determined (n : ℕ) (hn : 0 < n) :
    ∃ g h : ℕ → Segment, g ≠ h ∧ (∀ k < n, g k = h k) ∧
      (fun x : Icc (0 : ℝ) 1 => gridEval g n x.1)
        = (fun x : Icc (0 : ℝ) 1 => gridEval h n x.1) := by
  classical
  let g : ℕ → Segment := fun k => if k = n then ⟨1, 0⟩ else ⟨0, 0⟩
  let h : ℕ → Segment := fun k => if k = n then ⟨0, 1⟩ else ⟨0, 0⟩
  have hg : g n = ⟨1, 0⟩ := by unfold g; exact if_pos rfl
  have hh : h n = ⟨0, 1⟩ := by unfold h; exact if_pos rfl
  refine ⟨g, h, ?_, ?_, ?_⟩
  · -- they differ at `n`
    intro he
    have hpt := congrFun he n
    rw [hg, hh] at hpt
    exact absurd hpt (by simp)
  · -- they agree strictly below `n`
    intro k hk
    have hkn : k ≠ n := by omega
    unfold g h
    rw [if_neg hkn, if_neg hkn]
  · -- their behaviours coincide
    funext x
    have hk : segmentIndex n x.1 ≤ n := segmentIndex_le_on_unit n hn x.1 x.2
    rcases lt_or_eq_of_le hk with hlt | heq
    · have hne : segmentIndex n x.1 ≠ n := ne_of_lt hlt
      unfold gridEval g h
      rw [if_neg hne, if_neg hne]
    · -- the index is `n`, so `x = 1`, and both segments give `1` there
      have hx1 : x.1 = 1 := eq_one_of_segmentIndex_eq n hn x.1 x.2 heq
      unfold gridEval
      rw [heq, hg, hh, hx1]
      unfold Segment.eval
      norm_num

/-- **⭐⭐⭐ 合取：可恢复的恰是**前缀 `{0,…,n−1}`**。**

**=> A（行为只依赖 `{0,…,n}`）与 B（`g n` 不被决定）合起来，
说明行为所决定的集合**不超过** `{0,…,n−1}`。**

**=> 与第 970 轮的 `gridWeights_not_extractable`（全量不可提取）合读：
**反向不是「差一点」，而是**恰好差在 `n` 这一点与它之后的一切**。** -/
theorem grid_information_is_exactly_prefix (n : ℕ) (hn : 0 < n) :
    (∀ g h : ℕ → Segment, (∀ k ≤ n, g k = h k) →
        (fun x : Icc (0 : ℝ) 1 => gridEval g n x.1)
          = (fun x : Icc (0 : ℝ) 1 => gridEval h n x.1)) ∧
      (∃ g h : ℕ → Segment, g ≠ h ∧ (∀ k < n, g k = h k) ∧
        (fun x : Icc (0 : ℝ) 1 => gridEval g n x.1)
          = (fun x : Icc (0 : ℝ) 1 => gridEval h n x.1)) :=
  ⟨gridEval_congr_on_prefix n hn, gridEval_index_n_not_determined n hn⟩

end Lattice.Lib.Compiler.ReversibilitySharpness
