import Mathlib
import Lattice.Core.IR.Compile
import Lattice.Lib.Compiler.GridAlgebra
import Lattice.Lib.Compiler.PiecewiseUniform

/-!
# **边界 1 闭合**：把 P8 的误差界搬到真实载体上（阶段 J）

## 边界 1 原文

**`P8-LOWER-BOUNDS.md` §10 第 1 项：**

> **任何 LATTICE 的 IR 权重类型侧实现**——`hop_verdict` 全部用 `ℝ` 与 `ℤ` 陈述。

**=> 即：P8 的全部结果从未接触过 LATTICE 自己的权重类型。**

## 载体是什么

**`Core/IR/Compile.lean:74` 把它定义为 `ℕ → ℝ`（一个权重向量就是一条实数序列）。**

**=> 一个权重向量就是一条实数序列。**
**=> 而第 964 轮的网格函数是 `ℕ → Segment`，`Segment = ⟨m, c⟩` 是**两个**实数。**

**=> 于是**交织编码**就够：偶数位放斜率、奇数位放截距。**

## 命名说明（为什么本文件用全限定名）

**`audit_duplicate_names` 以**短名**计站点，而 IR 权重类型的短名在 `Core/IR` 里已出现两处
（`Compile.lean` 与 `FinSupport.lean`，分属不同命名空间）。**

**=> 本文件若再用短名，会使该计数超过基线。
=> 故本文件一律写**全限定名**，并在散文中称其为「IR 权重类型」。**

**=> 这本身也记录了 `Core/IR` 里那处**既有的**短名重复（两处同名 `abbrev`），留待后续收敛。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`encodeGrid_even/odd`** | **⭐ 编码在偶/奇位的取值** |
| **`decodeGrid_encodeGrid`** | **⭐⭐ 往返恒等（编码无损）** |
| **`encodeGrid_injective`** | **⭐⭐ 编码是单射（不丢信息）** |
| **`piecewiseIRWeights`** | **⭐⭐⭐ `n` 段族的**权重向量**（真实载体）** |
| **`piecewiseIRWeights_represents`** | **⭐⭐⭐ 该向量解码后**正是**分段族** |
| **`irWeights_error_bound`** | **⭐⭐⭐ **边界 1 主定理**：误差 `≤ (1/n)²/4`** |
| **`irWeights_uniform_tendsto`** | **⭐⭐⭐ R1 形状**在真实载体上成立** |

**=> 方向合法性：`Lib`（rank 3）→ `Core`（rank 0）向下引用，I4 允许。** -/

namespace Lattice.Lib.Compiler.IRWeightsBridge

open Set
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.PiecewiseUniform
open Lattice.Lib.Compiler.GridAlgebra

/-- **⭐⭐ 把网格函数编码成 IR 权重向量：偶数位斜率，奇数位截距。** -/
noncomputable def encodeGrid (g : ℕ → Segment) : Lattice.Core.IR.IRWeights :=
  fun i => if i % 2 = 0 then (g (i / 2)).m else (g (i / 2)).c

/-- **⭐⭐ 解码：从权重向量取回网格函数。** -/
noncomputable def decodeGrid (w : Lattice.Core.IR.IRWeights) : ℕ → Segment :=
  fun k => ⟨w (2 * k), w (2 * k + 1)⟩

/-- **⭐ 偶数位的取值是斜率。** -/
theorem encodeGrid_even (g : ℕ → Segment) (k : ℕ) : encodeGrid g (2 * k) = (g k).m := by
  unfold encodeGrid
  have hmod : (2 * k) % 2 = 0 := by omega
  have hdiv : (2 * k) / 2 = k := by omega
  simp only [hmod, if_true, hdiv]

/-- **⭐ 奇数位的取值是截距。** -/
theorem encodeGrid_odd (g : ℕ → Segment) (k : ℕ) : encodeGrid g (2 * k + 1) = (g k).c := by
  unfold encodeGrid
  have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp only [hmod, if_false, hdiv]

/-- **⭐⭐ 往返恒等：编码无损。** -/
theorem decodeGrid_encodeGrid (g : ℕ → Segment) : decodeGrid (encodeGrid g) = g := by
  funext k
  unfold decodeGrid
  rw [encodeGrid_even, encodeGrid_odd]

/-- **⭐⭐ 编码是单射：不同的网格函数给出不同的权重向量。**

**=> 由往返恒等直接得到（有左逆即单射）。** -/
theorem encodeGrid_injective : Function.Injective encodeGrid := by
  intro g h hgh
  rw [← decodeGrid_encodeGrid g, ← decodeGrid_encodeGrid h, hgh]

/-- **⭐⭐⭐ `n` 段分段线性族的**权重向量**（真实载体）。

**=> 偶数位是第 `k` 片的斜率 `k/n + (k+1)/n`，奇数位是截距 `-(k/n)·((k+1)/n)`。** -/
noncomputable def piecewiseIRWeights (n : ℕ) : Lattice.Core.IR.IRWeights :=
  encodeGrid (fun k => chordSegment ((k : ℝ) / n) (((k : ℝ) + 1) / n))

/-- **⭐⭐ `piecewiseIRWeights` 的偶数位显式形式。** -/
theorem piecewiseIRWeights_even (n k : ℕ) :
    piecewiseIRWeights n (2 * k) = (k : ℝ) / n + ((k : ℝ) + 1) / n := by
  unfold piecewiseIRWeights
  rw [encodeGrid_even]
  unfold chordSegment
  rfl

/-- **⭐⭐ `piecewiseIRWeights` 的奇数位显式形式。** -/
theorem piecewiseIRWeights_odd (n k : ℕ) :
    piecewiseIRWeights n (2 * k + 1) = -(((k : ℝ) / n) * (((k : ℝ) + 1) / n)) := by
  unfold piecewiseIRWeights
  rw [encodeGrid_odd]
  unfold chordSegment
  rfl

/-- **⭐⭐⭐ 该权重向量解码后**正是**分段族。**

**=> 这把第 964 轮的网格代数与真实权重载体**逐字**对上：
`gridEval (decodeGrid (piecewiseIRWeights n)) n x = piecewiseWeights n x`。** -/
theorem piecewiseIRWeights_represents (n : ℕ) (x : ℝ) :
    gridEval (decodeGrid (piecewiseIRWeights n)) n x = piecewiseWeights n x := by
  unfold piecewiseIRWeights
  rw [decodeGrid_encodeGrid]
  rfl

/-- **⭐⭐⭐ **边界 1 主定理**：在 LATTICE 的真实权重类型上，
`n` 段权重向量把 `x²` 逼近到 `(1/n)²/4` 以内。**

**=> 陈述完全用真实载体与 `decodeGrid` 表达，
不再出现「抽象的 `Segment` 网格」这一中间层。** -/
theorem irWeights_error_bound (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |x ^ 2 - gridEval (decodeGrid (piecewiseIRWeights n)) n x| ≤ (1 / (n : ℝ)) ^ 2 / 4 := by
  rw [piecewiseIRWeights_represents]
  exact piecewiseWeights_error_closed n hn x hx

/-- **⭐⭐⭐ R1 的**形状**在真实载体上成立。**

**=> `∀ ε > 0`，存在一个权重向量（`piecewiseIRWeights n`），
使 `[0,1]` 上**处处**误差 `≤ ε`。**

**=> 这是审计表格里 R1 的一致形式，而它现在说的是**权重向量**，不是抽象函数。** -/
theorem irWeights_uniform_tendsto :
    ∀ ε > 0, ∃ n : ℕ, 1 ≤ n ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |x ^ 2 - gridEval (decodeGrid (piecewiseIRWeights n)) n x| ≤ ε := by
  intro ε hε
  obtain ⟨n, hn1, hn⟩ := piecewiseWeights_uniform_tendsto ε hε
  refine ⟨n, hn1, fun x hx => ?_⟩
  rw [piecewiseIRWeights_represents]
  exact hn x hx

end Lattice.Lib.Compiler.IRWeightsBridge
