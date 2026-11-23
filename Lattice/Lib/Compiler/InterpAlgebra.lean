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
open Lattice.Lib.Compiler.Samples
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

/-- **⭐⭐⭐ 二次项的**整域误差界**：`|x² + p·x + q − 插值| ≤ (1/n)²/4`。**

**⇒ 装配是三步，每一步都引用本文件或既有定理：**
1. `interpFamily_add` 把二次项拆成「`x·x` 部分」与「仿射部分」；
2. `interpFamily_affine` + `gridEval_affineFamily` 说仿射部分插值**精确**（误差零）；
3. `interpFamily_sq_error` 给剩下那支的界。

**⇒ 于是总误差**正好退化**为 `x²` 的界——不是「小于两项之和」这种弱说法。

**⇒ 这就是规划 §3.1 A.5 要的那一步：对一**类**（二次 + 仿射）给出整域界，
而不是对 `x²` 一个特例。** -/
theorem interpFamily_quad_error (p q : ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(x * x + (p * x + q)) - gridEval (interpFamily n (fun y : ℝ => y * y + (p * y + q))) n x|
      ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  -- **`x · x` 与 `x ^ 2` 通过 `pow_two` 对齐；不把两者当同一个东西。**
  have hfun : (fun y : ℝ => y * y) = (fun y : ℝ => y ^ 2) := by
    funext y
    rw [pow_two]
  -- **第一步：拆成两支。**
  have hsplit : interpFamily n (fun y : ℝ => y * y + (p * y + q))
      = gridAdd (interpFamily n (fun y : ℝ => y * y)) (interpFamily n (fun y : ℝ => p * y + q)) :=
    interpFamily_add n hn _ _
  rw [hsplit, gridEval_add]
  -- **第二步：仿射那支插值精确。**
  have haff : interpFamily n (fun y : ℝ => p * y + q) = affineFamily p q :=
    interpFamily_affine n hn p q
  rw [haff, gridEval_affineFamily]
  -- **第三步：剩下的差异只剩 `x·x` 那一项。**
  have hdiff : (x * x + (p * x + q))
        - (gridEval (interpFamily n (fun y : ℝ => y * y)) n x + (p * x + q))
      = x * x - gridEval (interpFamily n (fun y : ℝ => y * y)) n x := by
    ring
  rw [hdiff, hfun]
  -- **`x · x` 在左侧也要变成 `x ^ 2`：`hfun` 只改写了**函数**的位置。**
  rw [← pow_two x]
  exact interpFamily_sq_error n hn x hx

/-- **⭐⭐⭐ 二次项的**产物层**整域界。**

**⇒ 与族层那条相比，本条多的只有**一次产物往返**（`evalAt_ofSegments`）。**
**⇒ 它是可用形式：调用者拿到的是产物的 `evalAt`，而不是一个族的网格求值。** -/
theorem quad_artifact_bound (p q : ℝ) (r : CompileRecipe)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ v : ℝ,
      (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
          (Target.family r (.interp (fun y : ℝ => y * y + (p * y + q)))) dom r).evalAt x = some v
        ∧ |(x * x + (p * x + q)) - v| ≤ (1 / (r.n : ℝ)) ^ 2 / 4 := by
  refine ⟨gridEval (interpFamily r.n (fun y : ℝ => y * y + (p * y + q))) r.n x, ?_, ?_⟩
  · exact Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments _ dom r x
  · exact interpFamily_quad_error p q r.n r.hn x hx


/-- **⭐⭐ 弦对**数乘**线性（与 `chordOf_add` 合起来，弦是**仿射映射**）。** -/
theorem chordOf_smul (k : ℝ) (f : ℝ → ℝ) (a b : ℝ) (h : a ≠ b) :
    chordOf (fun x => k * f x) a b
      = (⟨k * (chordOf f a b).m, k * (chordOf f a b).c⟩ : Segment) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [chordOf, chordSlope]
  congr 1
  · field_simp
    ring
  · field_simp
    ring

/-- **⭐⭐ 插值族对数乘线性**（与既有 `gridEval_smul` 配对）。 -/
theorem interpFamily_smul (n : ℕ) (hn : 0 < n) (k : ℝ) (f : ℝ → ℝ) :
    interpFamily n (fun x => k * f x) = gridSmul k (interpFamily n f) := by
  funext j
  exact chordOf_smul k f _ _ (endpoints_ne n hn j)

/-- **⭐⭐ 一般二次项的插值族拆成两支之和。** -/
theorem interpFamily_quadFun (n : ℕ) (hn : 0 < n) (a p q : ℝ) :
    interpFamily n (quadFun a p q)
      = gridAdd (gridSmul a (interpFamily n (fun y : ℝ => y * y)))
          (interpFamily n (fun y : ℝ => p * y + q)) := by
  have hsplit : quadFun a p q = fun y : ℝ => a * (y * y) + (p * y + q) := rfl
  rw [hsplit, interpFamily_add n hn (fun y : ℝ => a * (y * y)) (fun y : ℝ => p * y + q)]
  rw [interpFamily_smul n hn a (fun y : ℝ => y * y)]

/-- **⭐⭐⭐ 一般二次项的整域界：误差按 `|a|` **缩放**。**

**⇒ `|a·x·x + (p·x+q) − 插值| ≤ |a| · (1/n)²/4`。**

**⇒ 为何是 `|a|` 而不是 `a`：`a < 0` 时误差不变号，故界必须取绝对值——
这也是三角不等式无法直接应用、而必须用 `abs_mul` 的原因。** -/
theorem interpFamily_quadFun_error (a p q : ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |quadFun a p q x - gridEval (interpFamily n (quadFun a p q)) n x|
      ≤ |a| * ((1 / (n : ℝ)) ^ 2 / 4) := by
  rw [interpFamily_quadFun n hn a p q, gridEval_add, gridEval_smul]
  have haff : interpFamily n (fun y : ℝ => p * y + q) = affineFamily p q :=
    interpFamily_affine n hn p q
  rw [haff, gridEval_affineFamily]
  have hdiff : quadFun a p q x
        - (a * gridEval (interpFamily n (fun y : ℝ => y * y)) n x + (p * x + q))
      = a * (x * x - gridEval (interpFamily n (fun y : ℝ => y * y)) n x) := by
    show a * (x * x) + (p * x + q)
        - (a * gridEval (interpFamily n (fun y : ℝ => y * y)) n x + (p * x + q))
      = a * (x * x - gridEval (interpFamily n (fun y : ℝ => y * y)) n x)
    ring
  rw [hdiff, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
  have hfun : (fun y : ℝ => y * y) = (fun y : ℝ => y ^ 2) := by
    funext y
    rw [pow_two]
  rw [hfun, ← pow_two x]
  exact interpFamily_sq_error n hn x hx

/-- **⭐⭐⭐ 一般二次项的**产物层**界。** -/
theorem quadFun_artifact_bound (a p q : ℝ) (r : CompileRecipe)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ v : ℝ,
      (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
          (Target.family r (.interp (quadFun a p q))) dom r).evalAt x = some v
        ∧ |quadFun a p q x - v| ≤ |a| * ((1 / (r.n : ℝ)) ^ 2 / 4) := by
  refine ⟨gridEval (interpFamily r.n (quadFun a p q)) r.n x, ?_, ?_⟩
  · exact Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments _ dom r x
  · exact interpFamily_quadFun_error a p q r.n r.hn x hx

end Lattice.Lib.Compiler.InterpAlgebra