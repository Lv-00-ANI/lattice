import Mathlib
import Lattice.Lib.Compiler.ChordGeneral

/-!
# **网格代数**：分段线性族的**堆叠与组合构造**（阶段 I，P8 边界 3 最后一环）

## 本文件补的是什么

**P8 §10 边界 3 的原表述是「缺完整表达定理（**堆叠/组合构造**）》」。**
**第 960–963 轮补齐了：一般弦、精确表示、一般误差界、凸性路线、二阶导数界。
**=> 唯一剩下的就是**堆叠与组合**这一层。本文件补齐它。**

## 构造

**把「`n` 段分段线性函数」直接建成一个**代数对象**：
`ℕ → Segment`（每个索引给一段仿射）。求值即按 `segmentIndex` 查表。**

```lean
def gridEval (g : ℕ → Segment) (n : ℕ) (x : ℝ) : ℝ := (g (segmentIndex n x)).eval x
def gridAdd  (g h : ℕ → Segment) : ℕ → Segment := fun k => ⟨(g k).m + (h k).m, (g k).c + (h k).c⟩
def gridNeg  (g : ℕ → Segment)   : ℕ → Segment := fun k => ⟨-(g k).m, -(g k).c⟩
def gridSmul (a : ℝ) (g : ℕ → Segment) : ℕ → Segment := fun k => ⟨a * (g k).m, a * (g k).c⟩
```

**=> 于是「组合」有了精确含义：网格函数的加法、取负、数乘**逐段**进行，
且求值与这些运算**交换**（`gridEval_add` 等三条）。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`gridEval_add/neg/smul`** | **⭐⭐ 求值与加/负/数乘交换（族是向量空间）** |
| **`gridEval_affine`** | **⭐⭐ 仿射函数是网格函数** |
| **`affine_in_grid`** | **⭐⭐⭐ 表达力：任何仿射函数都在族内（误差为 0）** |
| **`interp_is_grid`** | **⭐⭐⭐ `piecewiseInterp` **就是**网格函数（同一族，不是新族）** |
| **`stacked_error_bound`** | **⭐⭐⭐ **堆叠**：两级逼近复合，误差**相加**（`ε₁ + ε₂`）** |

## 为什么「误差相加」是堆叠的正确内容

**真实流水线是**多级**的：符号 → 中间表示 → 权重，每一跳都引入误差。**
**=> 若第一跳误差 `≤ ε₁`、第二跳 `≤ ε₂`，则端到端误差 `≤ ε₁ + ε₂`。**

**=> `stacked_error_bound` 就是这条**预算律**，且它是纯三角不等式，与具体载体无关。** -/

namespace Lattice.Lib.Compiler.GridAlgebra

open Set
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.ChordGeneral

/-- **⭐⭐ 网格函数：每个索引给一段仿射，按 `segmentIndex` 查表求值。** -/
noncomputable def gridEval (g : ℕ → Segment) (n : ℕ) (x : ℝ) : ℝ :=
  (g (segmentIndex n x)).eval x

/-- **⭐⭐ 逐段相加。** -/
def gridAdd (g h : ℕ → Segment) : ℕ → Segment :=
  fun k => ⟨(g k).m + (h k).m, (g k).c + (h k).c⟩

/-- **⭐⭐ 逐段取负。** -/
def gridNeg (g : ℕ → Segment) : ℕ → Segment :=
  fun k => ⟨-(g k).m, -(g k).c⟩

/-- **⭐⭐ 逐段数乘。** -/
def gridSmul (a : ℝ) (g : ℕ → Segment) : ℕ → Segment :=
  fun k => ⟨a * (g k).m, a * (g k).c⟩

/-- **⭐⭐ 求值与加法交换。** -/
theorem gridEval_add (g h : ℕ → Segment) (n : ℕ) (x : ℝ) :
    gridEval (gridAdd g h) n x = gridEval g n x + gridEval h n x := by
  unfold gridEval gridAdd Segment.eval
  simp only
  ring

/-- **⭐⭐ 求值与取负交换。** -/
theorem gridEval_neg (g : ℕ → Segment) (n : ℕ) (x : ℝ) :
    gridEval (gridNeg g) n x = -(gridEval g n x) := by
  unfold gridEval gridNeg Segment.eval
  simp only
  ring

/-- **⭐⭐ 求值与数乘交换。** -/
theorem gridEval_smul (a : ℝ) (g : ℕ → Segment) (n : ℕ) (x : ℝ) :
    gridEval (gridSmul a g) n x = a * gridEval g n x := by
  unfold gridEval gridSmul Segment.eval
  simp only
  ring

/-- **⭐⭐ 仿射函数作为网格函数（所有段相同）。** -/
def affineGrid (c d : ℝ) : ℕ → Segment := fun _ => ⟨c, d⟩

/-- **⭐⭐ 仿射网格函数的求值。** -/
theorem gridEval_affine (c d : ℝ) (n : ℕ) (x : ℝ) :
    gridEval (affineGrid c d) n x = c * x + d := by
  unfold gridEval affineGrid Segment.eval
  simp only

/-- **⭐⭐⭐ 表达力：任何仿射函数都在网格族内，且**精确**。**

**=> 与第 962 轮的 `piecewiseInterp_affine_exact` 一致，
但这里是从**代数封闭性**角度看：仿射函数是网格代数的元素。** -/
theorem affine_in_grid (c d : ℝ) (n : ℕ) :
    ∃ g : ℕ → Segment, ∀ x : ℝ, gridEval g n x = c * x + d :=
  ⟨affineGrid c d, fun x => gridEval_affine c d n x⟩

/-- **⭐⭐⭐ `piecewiseInterp` **就是**网格函数（同一族，不是新族）。**

**=> 这把第 960 轮的分段插值族与本文件的网格代数**对接**：
插值族 = 由 `chordOf` 逐片生成的网格函数。
=> 所以「网格代数」不是另起一套，而是同一对象的代数化表述。** -/
theorem interp_is_grid (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    piecewiseInterp f n x
      = gridEval (fun k => chordOf f ((k : ℝ) / n) (((k : ℝ) + 1) / n)) n x := by
  unfold piecewiseInterp gridEval
  rfl

/-- **⭐⭐⭐ **堆叠律**：两级逼近复合，误差**相加**。**

**=> 陈述：若第一级把 `f` 逼近到 `ε₁` 内（用任意 `g`），
第二级把 `g` 逼近到 `ε₂` 内（用网格函数 `hs`），
则端到端把 `f` 逼近到 `ε₁ + ε₂` 内。**

**=> 这是纯三角不等式，与载体无关——但也正是**多级流水线**的误差预算律：
**符号 → 中间表示 → 权重，每一跳的误差在端到端相加。** -/
theorem stacked_error_bound (f g : ℝ → ℝ) (hs : ℕ → Segment) (n : ℕ) (ε₁ ε₂ : ℝ)
    (h1 : ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ ε₁)
    (h2 : ∀ x ∈ Icc (0 : ℝ) 1, |g x - gridEval hs n x| ≤ ε₂) :
    ∀ x ∈ Icc (0 : ℝ) 1, |f x - gridEval hs n x| ≤ ε₁ + ε₂ := by
  intro x hx
  have hsplit : f x - gridEval hs n x = (f x - g x) + (g x - gridEval hs n x) := by ring
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add (h1 x hx) (h2 x hx))

end Lattice.Lib.Compiler.GridAlgebra
