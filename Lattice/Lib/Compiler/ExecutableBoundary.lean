import Mathlib
import Lattice.Lib.Compiler.WeightSequence
import Lattice.Lib.Compiler.PiecewiseWeights
import Lattice.Lib.Compiler.GridAlgebra

/-!
# **可执行边界：在 `ℚ` 上求值，并证明它与 `ℝ` 模型一致**（阶段 R，`STATE-FINAL` §3.1）

## 那一格记的是 0/4，理由是三条路线各要付代价

**`STATE-FINAL.md` §3.1 记录：**

> **现状**：权重是 `ℝ` 上的 `noncomputable` 定义，`#eval` 直接报 "no executable code"。
>
> | 路线 | 代价 |
> |:--|:--|
> | `ℝ` → `Float` | **失去大部分精确性定理**——本库所有界都是 `ℝ` 上的 |
> | FFI 到外部张量库 | **与目标「不实现引擎/模型/训练框架」直接冲突** |
> | 生成 Python 代码 | **是代码生成，不是定理**；生成器的正确性另需证明 |

**⇒ 三条路线都要求**放弃**某样东西。本文档因此把这一格留作「需要所有者决策」。**

## 本文件走的是第四条：**不替换，而是并行**

**关键观察：`ℝ` 上的定理之所以不可执行，是因为 `ℝ` 不可计算；但**不需要替换 `ℝ`**——**

**=> 在 `ℚ` 上**另建一套可执行定义**，并证明它与 `ℝ` 模型**逐点一致**。**

| 对象 | `ℝ` 模型 | `ℚ` 模型（可执行） | 一致性定理 |
|:--|:--|:--|:--|
| **段** | `Segment`（`m c : ℝ`） | **`SegmentRat`（`m c : ℚ`）** | **`evalRat_coe`** |
| **分段索引** | `segmentIndex`（`Nat.floor` on `ℝ`） | **`segmentIndexRat`（`Rat.floor`）** | **`segmentIndexRat_coe`** |
| **网格求值** | `gridEval` | **`gridEvalRat`** | **`gridEvalRat_coe`** |

**⇒ 于是「可执行」与「`ℝ` 上的界」**同时成立**：执行走 `ℚ`，一切误差界定理原样保留。**

## 为什么这不算擅自选择

**§3.1 的三条路线都要求**放弃**某物（精确性、范围边界、或定理性）。
第四条不要求放弃任何一项：**

- **不失去 `ℝ` 定理**——它们全部仍在，本文档不改动任何一条；
- **不违反范围边界**——`ℚ` 是 Lean 自带的，无 FFI、无外部库；
- **不是代码生成**——每个 `ℚ` 定义都是 Lean 里的 `def`，一致性是定理。

**=> 故它落在「没有任何路线是废止的，只要可做那就做」之内，而不需要所有者先做取舍。**

## 关键的已有引理

**`Rat.floor_cast : ∀ {α} [LinearOrderedField α] [FloorRing α] (x : ℚ), ⌊↑x⌋ = ⌊x⌋`**

**=> 这一条使 `segmentIndex` 的一致性成为一次改写，而不是一场攻坚战。**
**=> 也就是说：可执行边界之所以一直记 0/4，**不是**因为数学上做不到，而是因为没有人查过这条引理在库里。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`SegmentRat`** | **⭐⭐ `ℚ` 上的仿射段** |
| **`SegmentRat.evalRat_coe`** | **⭐⭐⭐ 段求值在 `ℚ` 与 `ℝ` 上一致** |
| **`segmentIndexRat_coe`** | **⭐⭐⭐ 分段索引在 `ℚ` 与 `ℝ` 上一致** |
| **`gridEvalRat`** | **⭐⭐⭐ 可执行的网格求值** |
| **`gridEvalRat_coe`** | **⭐⭐⭐ 整个网格求值一致——本文件的核心** |
| **`gridEvalRat_witness`** | **⭐⭐ 一个**具体数值**的可执行计算（`norm_num` 直接算出）** | -/

namespace Lattice.Lib.Compiler

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.GridAlgebra

/-- **⭐⭐ `ℚ` 上的仿射段：斜率与截距都是有理数。**

**=> 与 `Segment` 逐字段对应，故 `toReal` 是逐字段的强制转换。** -/
structure SegmentRat where
  /-- 斜率 -/
  m : ℚ
  /-- 截距 -/
  c : ℚ

/-- **⭐ `ℚ` 段到 `ℝ` 段的强制转换（逐字段）。** -/
def SegmentRat.toReal (s : SegmentRat) : Segment := ⟨(s.m : ℝ), (s.c : ℝ)⟩

/-- **⭐⭐ `ℚ` 上的段求值 `m·x + c`——这是**可计算**的。** -/
def SegmentRat.evalRat (s : SegmentRat) (x : ℚ) : ℚ := s.m * x + s.c

/-- **⭐⭐⭐ 段求值在 `ℚ` 与 `ℝ` 上一致。** -/
theorem SegmentRat.evalRat_coe (s : SegmentRat) (x : ℚ) :
    ((s.evalRat x : ℚ) : ℝ) = s.toReal.eval (x : ℝ) := by
  unfold SegmentRat.evalRat SegmentRat.toReal Segment.eval
  push_cast
  ring

/-- **⭐⭐ `ℚ` 上的分段索引。**

**=> `Rat.floor` 是**可计算**的（整数除法），而 `Nat.floor` on `ℝ` 不是。** -/
def segmentIndexRat (n : ℕ) (x : ℚ) : ℕ := (Rat.floor (n * x)).toNat

/-- **⭐⭐⭐ 分段索引在 `ℚ` 与 `ℝ` 上一致。**

**=> 由 `Rat.floor_cast`（`⌊↑x⌋ = ⌊x⌋`）一次改写完成——这就是为什么这一格做得到。** -/
theorem segmentIndexRat_coe (n : ℕ) (x : ℚ) :
    segmentIndex n (x : ℝ) = segmentIndexRat n x := by
  have h : ((n * x : ℚ) : ℝ) = (n : ℝ) * (x : ℝ) := by push_cast; ring
  have hf : ⌊((n * x : ℚ) : ℝ)⌋ = Rat.floor (n * x) := Rat.floor_cast (n * x)
  show (⌊(n : ℝ) * (x : ℝ)⌋).toNat = (Rat.floor (n * x)).toNat
  rw [← h, hf]

/-- **⭐⭐⭐ 可执行的网格求值：与 `gridEval` 同构，但全部在 `ℚ` 上。** -/
def gridEvalRat (g : ℕ → SegmentRat) (n : ℕ) (x : ℚ) : ℚ :=
  (g (segmentIndexRat n x)).evalRat x

/-- **⭐⭐⭐ 本文件的核心：整个网格求值在 `ℚ` 与 `ℝ` 上一致。**

**=> 于是下游可以**执行**求值（走 `ℚ`），而所有 `ℝ` 上的误差界定理**原样适用**。** -/
theorem gridEvalRat_coe (g : ℕ → SegmentRat) (n : ℕ) (x : ℚ) :
    ((gridEvalRat g n x : ℚ) : ℝ)
      = gridEval (fun k => (g k).toReal) n (x : ℝ) := by
  unfold gridEvalRat gridEval
  rw [segmentIndexRat_coe]
  exact SegmentRat.evalRat_coe _ _

/-- **⭐⭐ 可执行性的具体见证：一个数值由 `norm_num` **直接算出**，
而不是由 `noncomputable` 定义「存在」。**

**=> `n = 4`、`x = 3/8`：`segmentIndexRat 4 (3/8) = 1`，
故求值取第 1 段 `⟨1, 0⟩`，得 `1 · 3/8 + 0 = 3/8`。** -/
theorem gridEvalRat_witness :
    gridEvalRat (fun _ => ⟨1, 0⟩) 4 (3 / 8 : ℚ) = 3 / 8 := by
  norm_num [gridEvalRat, segmentIndexRat, SegmentRat.evalRat, Rat.floor]

end Lattice.Lib.Compiler
