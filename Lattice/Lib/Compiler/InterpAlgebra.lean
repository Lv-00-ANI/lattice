import Lattice.Lib.Compiler.SymbolicEntry
import Lattice.Lib.Compiler.SecondDerivBound

/-!
# **插值族的代数：可加，且**继承**既有误差界**

## 这个文件补什么

第 1052 轮把 `Target` 推广成「一个族」（`interp f`），但只证了两件事：它在仿射函数上退化为常族、
以及产物层逐点精确。**⇒ 一个「族」要真的可用，还缺两条：**

1. **可加性**——否则无法把复合项（如 `x² + 仿射`）的误差预算拆开；
2. **与既有界的接线**——`x²` 的插值族必须**就是** `piecewiseIRWeights` 解码出的那个族，
   这样 `irWeights_error_bound`（`1/(4n²)`）不用重证就能用在新族上。

**⇒ 本文件给的就是这两条。它们让「推广」不丢东西：新族在 `x²` 上没有变弱，而是**正好同一条界**。**
-/

namespace Lattice.Lib.Compiler.InterpAlgebra

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.SymbolicEntry

/-- **相邻端点不同**：`n > 0` 时 `k/n ≠ (k+1)/n`。

**⇒ 这条是所有弦引理的共同前提，故单独命名；否则每个调用点都要重写一遍 `field_simp`。** -/
theorem endpoints_ne (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ((k : ℝ) / n) ≠ (((k : ℝ) + 1) / n) := by
  intro h
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp at h

/-- **⭐⭐ 弦是**可加**的。**

**⇒ `chordOf (f + g) a b` 的两个分量分别等于两支弦的分量之和。
这是「误差预算可以拆开」的代数根据：`f + g` 的插值误差被两支各自的误差所控。** -/
theorem chordOf_add (f g : ℝ → ℝ) (a b : ℝ) (h : a ≠ b) :
    chordOf (fun x => f x + g x) a b
      = (⟨(chordOf f a b).m + (chordOf g a b).m,
          (chordOf f a b).c + (chordOf g a b).c⟩ : Segment) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [chordOf, chordSlope]
  congr 1
  · field_simp
    ring
  · field_simp
    ring

/-- **⭐⭐ 插值族可加。**

**⇒ `interpFamily n (f + g)` 逐点等于两支族的 `gridAdd`——与 `gridEval_add` 是一对，
故求值也相加。** -/
theorem interpFamily_add (n : ℕ) (hn : 0 < n) (f g : ℝ → ℝ) :
    interpFamily n (fun x => f x + g x) = gridAdd (interpFamily n f) (interpFamily n g) := by
  funext k
  exact chordOf_add f g _ _ (endpoints_ne n hn k)

/-- **⭐⭐⭐ `x²` 的插值族**就是** `piecewiseIRWeights` 解码出的族。**

**⇒ 这条把新族接到**既有**的 `irWeights_error_bound` 上：`chordOf_sq` 说弦与 `chordSegment` 一致，
而 `decodeGrid_encodeGrid` 说解码回到原族。**
**⇒ 于是「推广没有变弱」不是承诺，而是一条等式。** -/
theorem interpFamily_sq (n : ℕ) (hn : 0 < n) :
    interpFamily n (fun x : ℝ => x ^ 2) = decodeGrid (piecewiseIRWeights n) := by
  funext k
  rw [show interpFamily n (fun x : ℝ => x ^ 2) k
        = chordOf (fun x : ℝ => x ^ 2) ((k : ℝ) / n) (((k : ℝ) + 1) / n) from rfl]
  rw [chordOf_sq _ _ (endpoints_ne n hn k)]
  unfold piecewiseIRWeights
  rw [decodeGrid_encodeGrid]

/-- **⭐⭐⭐ `x²` 的插值族满足既有的整域界。**

**⇒ 与 `irWeights_error_bound` **逐字相同**的结论，但陈述在**新族**上。
**⇒ 这条是本文件的目的：证明「一般族」在最重要的特例上**不弱于**专用族。** -/
theorem interpFamily_sq_error (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ 2 - gridEval (interpFamily n (fun x : ℝ => x ^ 2)) n x|
      ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  rw [interpFamily_sq n hn]
  exact irWeights_error_bound n hn x hx

end Lattice.Lib.Compiler.InterpAlgebra